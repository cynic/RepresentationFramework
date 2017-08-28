module FinalEquation.CommonStructure.Utilities

let inline (<<<<) (i : uint32) n = i <<< n ||| (i >>> (32 - n))
let inline (>>>>) (i : uint32) n = i >>> n ||| (i <<< (32 - n))

/// The designator input specifies the a-value that is being calculated
let kbit (t : Designator) = 
    let r = t.Round-1
    let i =
        match t.Var with
        | V.A -> (t.Bit+5)%32
        | V.V0 -> (t.Bit+6)%32
        | V.V1 -> (t.Bit+7)%32
        | _ -> failwithf "Requested k-bit for unexpected var %A; Designator=%O" t.Var t
    if r <= 19 then 0x5a827999u.[i]
    elif r <= 39 then 0x6ed9eba1u.[i]
    elif r <= 59 then 0x8f1bbcdcu.[i]
    else 0xca62c1d6u.[i]

let hexstringToBytes s =
    // validate a bit
    let validchars = "0123456789abcdef" |> Seq.toArray
    if s |> Seq.exists (fun x -> System.Array.BinarySearch(validchars, x) < 0) then
        None
    else
        s
        |> Seq.pairwise
        |> Seq.mapi (fun i item -> if i%2=0 then Some item else None)
        |> Seq.choose id
        |> Seq.map (fun (a,b) -> byte (sprintf "0x%c%c" a b))
        |> Seq.toArray
        |> Some

let bitProgression start ``end`` = 
    Seq.unfold (fun (r, i) -> 
        if r = ``end`` then None
        else 
            let nextI = (i + 31) % 32
                
            let nextR = 
                if nextI = 26 then r + 1
                else r
            Some((r, i), (nextR, nextI))) start

let datawordGenerator seed = 
    let r = System.Random seed
    fun len -> 
        if len > 447 then invalidArg "len" "A length > 447 goes over the size of a single SHA-1 chunk"
        let template = 
            [| 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; 0u; uint32 len |]
        template.[len / 32] <- 0x80000000u >>> (len % 32)
        let mask = 
            Array.init 16 (fun i -> 
                if i < len / 32 then 0xffffffffu
                elif i = len / 32 then 
                    { 0..len % 32 } |> Seq.fold (fun state item -> state ||| (0x80000000u >>> item)) 0u
                else 0u // must be > len/32
                        )
        Seq.initInfinite 
            (fun _ -> 
            Array.init 16 (fun _ -> r.Next(System.Int32.MinValue, System.Int32.MaxValue) |> uint32) 
            |> Array.mapi (fun i item -> (item &&& mask.[i]) ||| template.[i]))

let traditionalExpansion (datawords : uint32 []) = 
    let words = Array.append datawords (Array.zeroCreate 64)
    for i = 16 to 79 do
        words.[i] <- (words.[i - 3] ^^^ words.[i - 8] ^^^ words.[i - 14] ^^^ words.[i - 16]) <<<< 1
    words

/// Convert /bytes/ into a sequence of 1s and 0s
let bitstream bytes =
    let convert b =
        let convert' b =
            seq {
                if b &&& 0b10000000uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b01000000uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00100000uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00010000uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00001000uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00000100uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00000010uy > 0uy then yield 1uy else yield 0uy
                if b &&& 0b00000001uy > 0uy then yield 1uy else yield 0uy
            }
        convert' b
    bytes |> Seq.collect convert

/// Convert 32 bits to a word.
let inline bitsToWord bits =
    bits |> Seq.fold 
        (fun (idx, final) bit -> idx-1, final ||| ((uint32 bit) <<< idx))
        (31, 0u)
    |> snd

let bytesToHashInput message dwlen =
    let bits = [|
        let original = message |> bitstream |> Seq.take dwlen |> Seq.toArray
        yield! original
        yield 1uy
        let bits_to_make_up = 512 - ((original.Length+65) % 512)
        yield! Seq.init bits_to_make_up (fun _ -> 0uy)
        let origLength = original.LongLength
        yield! bitstream [|
            origLength >>> 56 |> byte
            origLength >>> 48 |> byte
            origLength >>> 40 |> byte
            origLength >>> 32 |> byte
            origLength >>> 24 |> byte
            origLength >>> 16 |> byte
            origLength >>> 8 |> byte
            origLength |> byte
        |]
    |]
    let datawords =
        bits
        |> Seq.chunkBySize 32
        |> Seq.map bitsToWord
        |> Seq.toArray
    traditionalExpansion datawords

/// Gives results back in the reverse order that processChunk does
let processChunk_lessalloc (words : _ []) = 
    let getK i = 
        if i <= 19 then 0x5a827999u
        elif i <= 39 then 0x6ed9eba1u
        elif i <= 59 then 0x8F1BBCDCu
        else 0xca62c1d6u
    
    let spliffle x px ppx pppx ppppx i = 
        let b = px
        let c = ppx <<<< 30
        let d = pppx <<<< 30
        let e = ppppx <<<< 30
        
        let f, k = 
            let firstNum = 
                if i <= 19 then (b &&& c) ||| ((~~~b) &&& d)
                elif i <= 39 then (b ^^^ c ^^^ d)
                elif i <= 59 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
                else (b ^^^ c ^^^ d)
            firstNum, getK i
        
        let newX = (x <<<< 5) + f + e + k + words.[i]
        newX
    
    let predecessors = [ 0x67452301u; 0xefcdab89u; 0x62eb73fau; 0x40c951d8u; 0x0f4b87c3u ]
    match predecessors |> List.map ref with
    | x :: px :: ppx :: pppx :: ppppx :: _ ->
        [| yield (!x <<<< 5)
           for i = 0 to 79 do
               let next = spliffle !x !px !ppx !pppx !ppppx i
               yield (next <<<< 5)
               ppppx := !pppx
               pppx := !ppx
               ppx := !px
               px := !x
               x := next |]
    | _ -> failwith "Design flaw - I should not be here! - must fix!"

/// Given an idx 0..159, return a Designator for that bit of the output hash.
let hashDesignator idx =    
    if idx < 0 || idx > 159 then failwith "hash designator must be in range [0..159]"
    let round = 80-idx/32
    let bit =
        match round with
        | 80 | 79 ->  (idx%32+27)%32 // align such that pos.27 = idx.0
        | _ -> (idx%32+25)%32
    { Round=round; Bit=bit; Var=V.A }

/// Given a Designator, return the bit [0..159] of the output hash that it maps to.
let hashDesignatorInv =
    let lut =
        {0..159} |> Seq.mapi (fun i v ->
            let d = hashDesignator v
            (d.Round, d.Bit), i
        ) |> Map.ofSeq
    fun (d : Designator) ->
        match lut |> Map.tryFind (d.Round, d.Bit) with
        | Some v -> v
        | None -> failwithf "There's no corresponding hash output bit for the designator %O" d

let hexStringToBits s =
    s |> Seq.collect (fun c -> // convert this to bits, which will go hi-lo, hi-lo, hi-lo, hi-lo, hi-lo
        match c with
        | '0' -> [|false;false;false;false|]
        | '1' -> [|false;false;false;true|]
        | '2' -> [|false;false;true;false|]
        | '3' -> [|false;false;true;true|]
        | '4' -> [|false;true;false;false|]
        | '5' -> [|false;true;false;true|]
        | '6' -> [|false;true;true;false|]
        | '7' -> [|false;true;true;true|]
        | '8' -> [|true;false;false;false|]
        | '9' -> [|true;false;false;true|]
        | 'a' -> [|true;false;true;false|]
        | 'b' -> [|true;false;true;true|]
        | 'c' -> [|true;true;false;false|]
        | 'd' -> [|true;true;false;true|]
        | 'e' -> [|true;true;true;false|]
        | 'f' -> [|true;true;true;true|]
        | _ -> failwith "Should match, didn't.  Not hex??"
    )

let hashToBits hash =
    assert (String.length hash = 160/4)
    hexStringToBits hash

/// Returns None if there's no solution
let gjeliminate (xs : (_[] * _) []) =
    // first, establish how many unique variables there are.
    let idx_to_var, var_to_idx =
        let idx_to_var = xs |> Seq.map fst |> Seq.concat |> Seq.distinct |> Seq.toArray
        let var_to_idx = idx_to_var |> Array.mapi (fun i x -> x, i) |> Map.ofSeq
        idx_to_var, var_to_idx
    // the length of the map = how many unique variables there are, and the mapped value is a unique index.
    let bitlen = idx_to_var.Length + 1 // + 1 for the augmented column.
    let eqnCount = xs.Length
    let vars =
        Array.init xs.Length (fun idx ->
            let bits = new System.Collections.BitArray(bitlen)
            let v, r = xs.[idx]
            for var in v do
                bits.Set(var_to_idx.[var], true)
            if r = 1uy then bits.Set(bitlen-1, true) // augmented.
            bits
        )
    let inline (^=) i j = vars.[i].Xor vars.[j] |> ignore
    let swap =
        let tmp = ref Unchecked.defaultof<System.Collections.BitArray>
        fun i j ->
            if i = j then
                ()
            else
                tmp := vars.[i]
                vars.[i] <- vars.[j]
                vars.[j] <- !tmp
    let (~%) (v : System.Collections.BitArray) =
        new System.String(seq { for b in v do if b then yield '1' else yield '0' } |> Seq.toArray)
    let printMatrix header =
        if header <> "" then printfn "%s" header
        vars |> Array.iter (fun x -> printfn "%s" %x)
    let rec geliminate rc = // the actual gaussian elimination.
        if rc = eqnCount || rc > bitlen-2 then
            () // all done!
        else
            let pivot =
                let candidates =
                    seq {
                        for i = rc to eqnCount-1 do
                            if vars.[i].[rc] then yield i
                    }
                if Seq.isEmpty candidates then None
                else Some (Seq.head candidates)
            match pivot with
            | Some pivot ->
                swap pivot rc
                // go through everything else, and xor them as necessary.
                for i = rc+1 to eqnCount-1 do
                    if vars.[i].[rc] then i ^= rc
            | None -> () // skip over, do nothing.
            geliminate (rc+1)
    geliminate 0
    //printMatrix "All done with Gaussian elimination!"
    let rec jeliminate rc =
        if rc = eqnCount || rc > bitlen-2 then
            () // all done!
        else
            if vars.[rc].[rc] then
                for i = rc-1 downto 0 do
                    if vars.[i].[rc] then i ^= rc
            //printMatrix (sprintf "After xor'ing (jelim @ diag #%d)" rc)
            jeliminate (rc+1)
    jeliminate 0
    //printMatrix "All done with Gauss-Jordan elimination!"
    // now convert back.
    let equations =
        vars
        |> Seq.map (fun arr ->
            seq {
                for i in 0..bitlen-2 do
                    if arr.[i] then yield idx_to_var.[i]
            } |> Seq.toArray
        )
    let results =
        vars |> Seq.map (fun arr -> if arr.[bitlen-1] then 1uy else 0uy)
    if Seq.exists2 (fun v r -> v = [||] && r = 1uy) equations results then
        None
    else
        Seq.zip equations results
        |> Seq.filter (fun (v,_) -> v <> [||])
        |> Seq.distinct
        //|> Seq.sort // purely for readability.
        |> Seq.toArray
        |> Some
