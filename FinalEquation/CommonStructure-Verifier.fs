[<AutoOpen>]
module FinalEquation.CommonStructure.Verification
open FinalEquation.CommonStructure.Utilities

/// The 'safety' parameter is the number of instances of random data to use.
type Verifier<'T>(dwlen : uint32, safety) = 
    
    let preprocessDataWords = 
        traditionalExpansion >> processChunk_lessalloc
    
    let checkData, actuals = 
        let cache = System.Collections.Generic.Dictionary()
        // now create the canaries.
        match cache.TryGetValue dwlen with
        | true, v -> v
        | false, _ -> 
            //System.Console.WriteLine "Generating canaries."
            let dwGen = datawordGenerator 12345
            
            let dwSeq = 
                dwGen (int dwlen)
                |> Seq.distinct
                |> Seq.take (min (2I ** int dwlen) safety |> int)
                |> Seq.toArray
            
            let actuals = dwSeq |> Array.map preprocessDataWords
            cache.[dwlen] <- (dwSeq, actuals)
            //System.Console.WriteLine "Canaries generated."
            dwSeq, actuals
    
    let sw = System.Diagnostics.Stopwatch()

    let verify evaluators p i point = 
        sw.Restart()
        let msgbuf = System.Collections.Generic.List()
        let anyFailures = 
            //if already_verified.[p].[i] then false
            //else
            evaluators
            |> Array.(*Parallel.*)mapi (fun j (checkDatum, evaluateAt) -> 
(*                
                if p >= 76 then
                    let s = sprintf "Evaluating (%d,%d), expecting %b, using point=%A" p i actuals.[j].[p].[i] point
                    System.Console.WriteLine s
*)
                let result = evaluateAt point
                let actual = actuals.[j]
                if actual.[p].[i] <> result then 
                    let msg = 
                        sprintf "Failure at a(%d,%d), length %d, checkData=%A: expected %b, got %b" p i dwlen 
                            checkDatum actual.[p].[i] result
                    msgbuf.Add msg
                    //System.Console.WriteLine("{0}", msg)
                    false
                else true)
            |> Array.exists ((=) false)
        sw.Stop()
        if anyFailures then 
            printfn "%A" (Seq.map id msgbuf)
            failwith "Failure during verification: abort!"
        elif sw.ElapsedMilliseconds > 200L then
            System.Console.WriteLine("p={0},i={1}, time taken={2}s", p, i, sw.Elapsed.TotalSeconds)

    //let already_verified : uint32 [] = Array.zeroCreate 80
    //member __.PreprocessDataWords xs = preprocessDataWords xs
    member __.CachedVerifierFor (repr : IRepresentation<'T>) =
        checkData
        |> Array.map (fun d ->
            match repr.EvaluationCache d with
            | Some f -> d, f
            | None -> d, repr.Evaluate d
        ) |> verify
        
    /// This isn't very efficient, better to use VerifierFor for verifying all points
    member __.VerifySinglePoint(p, i, repr : IRepresentation<'T>, point : 'T) = 
        __.CachedVerifierFor repr p i point

let verify dwlen repr (storage : IStorage<_>) limit =
    let verifier = Verifier(dwlen, 5I)
    let f = verifier.CachedVerifierFor repr
    for (r,i) in bitProgression (1, 26) limit do
        let key = { Round=r; Bit=i; Var=V.A }
        let value = storage.[key]
        f r i value
