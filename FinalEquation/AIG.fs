namespace FinalEquation.AIG

type AAG = 
    { /// The pre-doubled variable (complemented as necessary)
      Output : uint32
      /// The variables, in final form.  The actual literal value = (dwlen+1+arrayIdx) <<< 1
      Ands : (uint32 * uint32) [] }
    
    member __.Serialize = 
        let o = sprintf "%d" __.Output
        
        let a = 
            __.Ands
            |> Seq.map (fun (a, b) -> sprintf "%d,%d" a b)
            |> String.concat ";"
        sprintf "%s|%s" o a
    
    override __.ToString() = sprintf "%d|(%d clauses ~= %A)" __.Output __.Ands.Length __.Ands
    static member Deserialize(s : string) = 
        match s.Split '|' with
        | [| o; a |] -> 
            let o = uint32 o
            
            let a = 
                if System.String.IsNullOrEmpty a then Array.empty
                else 
                    a.Split ';' |> Array.map (fun s -> 
                                       let tuple = s.Split ','
                                       uint32 tuple.[0], uint32 tuple.[1])
            { Output = o
              Ands = a }
        | _ -> failwithf "Couldn't deserialize: %s" s

module ABCOptions =
#if LINUX 
    [<Literal>]
    let ABCExecutable = "./abc"
    
    [<Literal>]
    let OutputRoot = "/tmp/cleanstar"
    #else
    let [<Literal>] ABCExecutable = "abc.exe"
    let [<Literal>] OutputRoot = "C:\\Temp"
#endif
    let [<Literal>] ABCWriteCommand = "write_aiger" // '-c' makes it write in aig2 format
    // I would like to read in aig2 format as well, but can't find a format description!
    let [<Literal>] ABCQuietCommand = "-f"
        
    [<Literal>]
    let Tolerance = 3
    
    [<Literal>]
    let CombinedOutputIsZero = true

type ABCOperation = 
    // just two different ways to minimise.
    | MinimiseX
    | MinimiseY
    | Strash
    | Collapse

type ABCInterface(dwlen) =     
    static let uid = 
        let v = ref 0
        fun () -> System.Threading.Interlocked.Increment v
    
    let outputdir = 
        let od = ref None
        fun () -> 
            match !od with
            | Some v -> v
            | None -> 
                let _od = 
                    System.IO.Path.Combine [| ABCOptions.OutputRoot
                                              sprintf "output_%d" dwlen |]
                System.IO.Directory.CreateDirectory _od |> ignore
                od := Some _od
                _od
    
    let runCLIProcess exe args quietly = 
        use p = new System.Diagnostics.Process()
        p.StartInfo <- System.Diagnostics.ProcessStartInfo
                           (exe, UseShellExecute = false, CreateNoWindow = true,
                            Arguments = args, RedirectStandardOutput = true)
        p.Start() |> ignore
        if not quietly then
            let output = p.StandardOutput.ReadToEnd()
            printfn "===ABC OUTPUT BEGIN\n%s\n===ABC OUTPUT END" output
        p.WaitForExit()
    
    let runABC f_in f_out cmds quietly = 
        let f_script = sprintf "%s_script" f_in
        System.IO.File.Delete f_script
        let readCmd = sprintf "read_aiger %s" f_in
        let writeCmd = sprintf "%s %s" ABCOptions.ABCWriteCommand f_out
        
        let cmd = 
            [| yield readCmd
               yield! cmds
               yield writeCmd |]
        if not quietly then printfn "CMD-script %s" f_script
        using (System.IO.File.CreateText f_script) 
            (fun f_script_stream ->
                cmd |> Array.iter (fun x ->
                    if not quietly then printfn "CMD: %s" x;
                    f_script_stream.WriteLine x
                )
            )
        runCLIProcess ABCOptions.ABCExecutable (sprintf "%s %s" ABCOptions.ABCQuietCommand f_script) quietly
        //System.IO.File.Delete f_script
    
    let encodeInt = 
        function 
        | n when n < 128u -> [| byte n |]
        | x -> 
            Seq.unfold (fun state -> 
                if state = 0u then None
                else 
                    let next = state >>> 7
                    if next > 0u then Some(byte (state &&& 0x7fu) ||| 0x80uy, next)
                    else Some(byte (state &&& 0x7fu), 0u)) x
            |> Seq.toArray
    
    member __.WriteMultiOutputAiger(arr : _ [], outputs, fname) = 
        System.IO.File.Delete fname
        // before I create the AAG file, I need to know the number of ANDs, the number of inputs, and the maximum variable count.
        let maxInput = // this holds the UNDOUBLED input
            let mutable result = 0u
            for (a, b) in arr do
                let a' = a >>> 1
                let b' = b >>> 1
                if a' <= dwlen && a' > result then result <- a'
                if b' <= dwlen && b' > result then result <- b'
            for o in outputs do
                let o' = o >>> 1
                if o' <= dwlen && o' > result then result <- o'
            result
        
        let ands, outputs = //arr, outputs
            let ands = System.Collections.Generic.List(Array.length outputs)
            let vCache = System.Collections.Generic.Dictionary()
            
            let (&&&) a b = 
                if a > b then ands.Add(a, b)
                else ands.Add(b, a)
                (maxInput + uint32 ands.Count) <<< 1
            
            let rec evaluate doubled = 
                let undoubled = doubled >>> 1
                let neg = doubled % 2u
                match doubled with
                | 0u | 1u -> doubled // these are constants.
                | v when undoubled <= dwlen -> // this is a var
                    v
                | i -> 
                    match vCache.TryGetValue undoubled with
                    | true, v -> v ^^^ neg
                    | false, _ -> 
                        let v = 
                            let idx = undoubled - dwlen - 1u
                            let a, b = arr.[int idx]
                            let aFanout = evaluate a
                            let bFanout = evaluate b
                            aFanout &&& bFanout
                        vCache.[undoubled] <- v // just store the 'positive' version.
                        v ^^^ neg
            
            let new_fanouts = outputs |> Array.map evaluate
            assert (ands.Count <= arr.Length)
            ands.ToArray(), new_fanouts
        
        use f_stream = System.IO.File.Create fname
        
        let preamble = 
            let dwlen_diff = (dwlen - maxInput) <<< 1
            let headerText = 
                sprintf "aig %d %d 0 %d %d\n" (maxInput + uint32 ands.Length) maxInput (Array.length outputs) 
                    ands.Length // M I L O A
            let to_write = outputs |> Array.fold (fun state n -> 
                                          //let o = if n >>> 1 <= maxInput then n else n - dwlen_diff
                                          //assert (o <= ((uint32 ands.Length + maxInput) <<< 1) + 1u)
                                          sprintf "%s%d\n" state n //o
                                                                   ) headerText
            System.Text.Encoding.ASCII.GetBytes to_write
        f_stream.Write(preamble, 0, preamble.Length)
        let andLHSStart = maxInput + 1u
        ands |> Array.iteri (fun i (a, b) -> 
                    let lhs = (andLHSStart + uint32 i) <<< 1
                    let delta0 = lhs - a
                    let delta1 = a - b
                    assert (lhs > a)
                    assert (a >= b)
                    let encoded_a = encodeInt delta0
                    let encoded_b = encodeInt delta1
                    f_stream.Write(encoded_a, 0, encoded_a.Length)
                    f_stream.Write(encoded_b, 0, encoded_b.Length))
    
    member __.WriteAiger(aag, fname) = __.WriteMultiOutputAiger(aag.Ands, [| aag.Output |], fname)
    
    member __.ReadMultiOutputAiger fname = 
        // this maps AIG_input => actual_input
        let binStart, oValues, maxInput, aCount = 
            using (System.IO.File.OpenText fname) (fun f_stream -> 
                let bytesConsumed = ref 0
                let header = f_stream.ReadLine()
                bytesConsumed := header.Length + 1
                let iCount, aCount, oCount = 
                    let split = header.Split ' ' // aig; M; I; L; O; A
                    uint32 split.[2], uint32 split.[5], int split.[4]
                
                let oValues = 
                    Array.init oCount (fun i -> 
                        let line = f_stream.ReadLine()
                        bytesConsumed := !bytesConsumed + line.Length + 1
                        uint32 line)
                
                !bytesConsumed, oValues, iCount, aCount)
        
        use f_stream = System.IO.File.OpenRead fname
        f_stream.Seek(int64 binStart, System.IO.SeekOrigin.Begin) |> ignore
        let dataBytes = 
            Seq.unfold (fun state -> 
                if state = -1 then None
                else Some(byte state, f_stream.ReadByte())) (f_stream.ReadByte())
            |> Seq.toArray
        
        let decodeInt start = 
            let ``end`` = 
                let rec getBytes i = 
                    if dataBytes.[i] &&& 0x80uy > 0uy then getBytes (i + 1)
                    else i
                getBytes start
            
            let output = 
                let mutable result = 0u
                let mutable counter = 0
                for i = start to ``end`` do
                    result <- result ||| (uint32 (dataBytes.[i] &&& 0x7fuy) <<< counter * 7)
                    counter <- counter + 1
                result
            
            output, ``end`` + 1
        
        let rec getUInt32s offset remaining = 
            match remaining with
            | 0u -> Seq.empty
            | _ -> 
                seq { 
                    let a, nxtStart = decodeInt offset
                    let b, nxtStart = decodeInt nxtStart
                    yield a, b
                    yield! getUInt32s nxtStart (remaining - 1u)
                }
        
        let andLHSStart = maxInput + 1u
        let varMax = (maxInput <<< 1) + 1u
        let dwlen_diff = (dwlen - maxInput) <<< 1
        let andDeltas = getUInt32s 0 aCount
        
        let ands = 
            andDeltas
            |> Seq.mapi (fun i (delta0, delta1) -> 
                   let lhs = (uint32 i + andLHSStart) <<< 1
                   let rhs0 = lhs - delta0
                   let rhs1 = rhs0 - delta1
                   (if rhs0 <= varMax then rhs0
                    else rhs0 + dwlen_diff), 
                   (if rhs1 <= varMax then rhs1
                    else rhs1 + dwlen_diff))
            |> Seq.toArray
        
        // the rest of the file is stuff I don't care about.  Ignore it.
        let outputs = 
            oValues |> Array.map (fun oValue -> 
                           if oValue <= varMax then oValue
                           else oValue + dwlen_diff)
        
        outputs, ands
    
    member __.ReadAiger fname = 
        let outputs, ands = __.ReadMultiOutputAiger fname
        if outputs.Length <> 1 then failwithf "Expected 1 output, got %d outputs." outputs.Length
        { Output = outputs.[0]
          Ands = ands }
    
    member __.Filename fname = 
        System.IO.Path.Combine [| outputdir()
                                  fname |]
    
    member __.ManualEvaluate(f_in, f_out, what, ?quietly) = 
        let quietly = defaultArg quietly true
        let cmds = 
            match what with
            | MinimiseX -> //[| "st"; "compress2"; "resyn3"; "compress2" |]
                //[|"st"; "resyn2a"|]
                [|"st"; "resyn2"|] // resyn3 sometimes crashes ABC!
            | MinimiseY ->
                [|"st"; "resyn3"|] // so does resyn2 :-/
            | Collapse -> [| "logic"; "aig"; "collapse -r"; "strash" |]
            | Strash -> [| "strash" |]
        runABC f_in f_out cmds quietly
        System.IO.File.Exists f_out
    
    member __.AIGEvaluate(input : AAG, op, ?quietly) = 
        let quietly = defaultArg quietly true
        let f_in = __.Filename(sprintf "file_%d" <| uid())
        let f_out = sprintf "%s_out" f_in
        System.IO.File.Delete f_in
        System.IO.File.Delete f_out
        __.WriteAiger(input, f_in)
        // now, need to convert AAG => AIG
        let result = __.ManualEvaluate(f_in, f_out, op, quietly)
        if result then
            let data = __.ReadAiger f_out
            //System.IO.File.Delete f_in
            //System.IO.File.Delete f_out
            Some data
        else None
    
    member __.AIGEquivalent(i0 : AAG, i1 : AAG, ?quietly) = 
        let quietly = defaultArg quietly false
        let f_in0 = __.Filename(sprintf "file_%d.aig" <| uid())
        let f_in1 = __.Filename(sprintf "file_%d.aig" <| uid())
        System.IO.File.Delete f_in0
        System.IO.File.Delete f_in1
        __.WriteAiger(i0, f_in0)
        __.WriteAiger(i1, f_in1)
        // now, check for equivalence using 'cec'
        use p = new System.Diagnostics.Process()
        p.StartInfo <- System.Diagnostics.ProcessStartInfo
                           (ABCOptions.ABCExecutable, UseShellExecute = false, CreateNoWindow = true, 
                            Arguments = sprintf "-c \"read_aiger %s; cec %s\"" f_in0 f_in1, 
                            RedirectStandardOutput = true)
        p.Start() |> ignore
        let output = p.StandardOutput.ReadToEnd()
        p.WaitForExit()
        if not quietly then
            printfn "===CEC OUTPUT BEGIN\n%s\n===CEC OUTPUT END" output
(*
        if output.StartsWith "Primary input" then 
            // ummm.  Try again??
            // Edit: seems to have no effect.  No idea what's going on here?  Anyway.
            // Let's leave the files alone and return true.  We'll come back to them, I guess.  *shrug*...
            //System.Diagnostics.Debugger.Break ()
            //System.IO.File.Delete f_in0
            //System.IO.File.Delete f_in1
            //__.AIGEquivalent (i0, i1)
            true
        else 
*)
        let result = output.Contains "Networks are equivalent"
        if result then 
            System.IO.File.Delete f_in0
            System.IO.File.Delete f_in1
        else
            printfn "Filenames are: %s and %s\n%s" f_in0 f_in1 output
        result
    
    member __.AIGEvaluateInNewThread(input, op) = 
        async { 
            do! Async.SwitchToNewThread()
            return __.AIGEvaluate(input, op)
        }
        |> Async.RunSynchronously

open FinalEquation.CommonStructure

type Stats = { Ands : int; Ors : int; Xors : int; Nots : int; Ops : int }

type AndInverterGraph(dwlen : uint32) = 
    //let abc = ABCInterface(dwlen)
    //let keys = Keys(dwlen)
    //let verifier = Verifier(dwlen, 5I)
    let ctx = System.Collections.Generic.List()
    let varMax_binOp = (dwlen <<< 1) + 1u
    
    /// convert doubled value to idx value
    let idxOf x = (x >>> 1) - dwlen - 1u |> int
    
    /// convert idx value to (positive) doubled value
    let positiveNodeOf x = (dwlen <<< 1) + 2u + (uint32 x <<< 1)
    
    let opCount = ref 0
    let xorCount = ref 0
    let andCount = ref 0
    let orCount = ref 0
    let notCount = ref 0
    
    let _and (ctx : System.Collections.Generic.List<_>) (a : uint32) (b : uint32) = 
        opCount := !opCount + 1
        andCount := !andCount + 1
        match a, b with
        | 0u, _ | _, 0u -> 0u
        | 1u, x | x, 1u -> x
        | a, b when a = b -> a
        | a, b when a = b ^^^ 1u -> 0u
        | a, b -> 
            let processNormally() = 
                // I want the resulting fanout (for use in other expressions), AND I want the ctx to be changed.
                // I can assume that the appropriate uint32 fanouts already exist in ctx.
                let ctxCount = 
                    lock (ctx) (fun () -> 
                        ctx.Add(a, b)
                        ctx.Count)
                (dwlen + uint32 ctxCount) <<< 1
            if a > varMax_binOp && a % 2u = 0u then 
                let c, d = ctx.[idxOf a]
                if c = b || d = b then a
                else processNormally()
            elif b > varMax_binOp && b % 2u = 0u then 
                let c, d = ctx.[idxOf b]
                if c = a || d = a then b
                else processNormally()
            else processNormally()
    
    let _or (ctx : System.Collections.Generic.List<_>) (a : uint32) (b : uint32) = 
        opCount := !opCount + 1
        orCount := !orCount + 1
        match a, b with
        | 1u, _ | _, 1u -> 1u
        | 0u, x | x, 0u -> x
        | a, b when a = b -> a
        | a, b when a = b ^^^ 1u -> 1u
        | a, b -> 
            let ctxCount = 
                lock (ctx) (fun () -> 
                    ctx.Add(a ^^^ 1u, b ^^^ 1u)
                    ctx.Count)
            ((dwlen + uint32 ctxCount) <<< 1) + 1u
    
    let _xor (ctx : System.Collections.Generic.List<_>) (a : uint32) (b : uint32) = 
        opCount := !opCount + 1
        xorCount := !xorCount + 1
        match a, b with
        | 0u, x | x, 0u -> x
        | 1u, x | x, 1u -> x ^^^ 1u
        | a, b when a = b -> 0u
        | a, b when a = b ^^^ 1u -> 1u
        | a, b -> 
            lock (ctx) (fun () -> 
                ctx.Add(a, b)
                let o0 = (dwlen + uint32 ctx.Count) <<< 1
                ctx.Add(a ^^^ 1u, b ^^^ 1u)
                let o1 = o0 + 2u
                ctx.Add(o0 ^^^ 1u, o1 ^^^ 1u)
                o1 + 2u)

    let evaluatedFor (data : uint32[]) =
        let bs = System.Collections.BitArray((ctx.Count <<< 1) + (int dwlen <<< 1) + 3)
        bs.[1] <- true
        for i = 1 to int dwlen do
            let doubled = int (i <<< 1)
            bs.[doubled] <- data.[(i - 1) / 32].[(i - 1) % 32]
            bs.[doubled + 1] <- not bs.[doubled]
        let ands_start = int (dwlen <<< 1) + 2
        for i = 0 to ctx.Count-1 do
            let a, b = ctx.[i]
            let result = bs.[int a] && bs.[int b]
            let idx = ands_start + (i <<< 1)
            bs.[idx] <- result
            bs.[idx + 1] <- not result
        fun (fanout : uint32) -> bs.[int fanout]
    
    let evaluate (data : uint32[]) aag = 
        let bs = System.Collections.BitArray(max (int aag.Output) (2 * int dwlen) + 3)
        bs.[1] <- true
        for i = 1 to int dwlen do
            let doubled = int (i <<< 1)
            bs.[doubled] <- data.[(i - 1) / 32].[(i - 1) % 32]
            bs.[doubled + 1] <- not bs.[doubled]
        let ands_start = int (dwlen <<< 1) + 2
        let ands_end = int <| (aag.Output >>> 1) - dwlen - 1u
        for i = 0 to ands_end do
            let a, b = aag.Ands.[i]
            let result = bs.[int a] && bs.[int b]
            let idx = ands_start + (i <<< 1)
            bs.[idx] <- result
            bs.[idx + 1] <- not result
        bs.[int aag.Output]
        
    member __.IdxToPositiveNode = positiveNodeOf
    member __.NodeToIdx = idxOf
    member __.AAG with get () = { Output = positiveNodeOf <| ctx.Count-1; Ands = ctx.ToArray() }
    member __.Stats = { Ands= !andCount; Ors= !orCount; Nots = !notCount; Xors = !xorCount; Ops = !opCount }

    interface IRepresentation<uint32> with
        
        member __.Constants = 
            { Zero = 0u
              One = 1u }
        
        member __.And a b = _and ctx a b
        member __.Or a b = _or ctx a b
        member __.Xor a b = _xor ctx a b
        
        member __.Not x = 
            opCount := !opCount + 1
            notCount := !notCount + 1
            x ^^^ 1u
        
        member __.MakeVariable i = (uint32 (i + 1u)) <<< 1
        member __.Evaluate data fanout =  evaluate data { Output = fanout; Ands = ctx.ToArray() }
        member __.EvaluationCache data = Some (evaluatedFor data)
        member __.IsZero x = x = 0u
        member __.IsOne x = x = 1u
        member __.Dispose () = ()