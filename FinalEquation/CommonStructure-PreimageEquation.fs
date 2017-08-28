[<AutoOpen>]
module FinalEquation.CommonStructure.PreimageEquation

open FinalEquation.CommonStructure.Constants
open FinalEquation.CommonStructure.Utilities

let hash message len =
    let processChunk (h0, h1, h2, h3, h4) (words : uint32[]) =
        // printfn "Words = %A" words
        //printfn "["
        let a_values = Array.zeroCreate 80
        let rec spliffle a b c d e i =
            printfn "Round %02d, a=%08x b=%08x c=%0x8 d=%08x e=%08x" i a b c d e
            //printfn "   [0x%08xu; 0x%08xu; 0x%08xu; 0x%08xu; 0x%08xu];" a b c d e
            match i with
            | 80 ->
            // a78.31 = w79.31 ^ a73.29 ^ w78.31
            // k78.31 is 0.
                let rhs, rel =
                    let k78_31 = 0u // I know it's 0.
                    let a77_4 = (a_values.[77] <<<< 5) &&& 1u
                    let a76_31 = a_values.[76] &&& 1u
                    let a75_29 = (a_values.[75] >>> 2) &&& 1u
                    let a74_29 = (a_values.[74] >>> 2) &&& 1u
                    let a73_29 = (a_values.[73] >>> 2) &&& 1u
                    let w78_31 = words.[78] &&& 1u
                    let basicform = (k78_31 + a77_4 + (a74_29 ^^^ a73_29 ^^^ w78_31)) % 2u
                    if a75_29 ^^^ a76_31 = 1u then
                       basicform, (<>)
                    else
                        basicform, (=)
                let lhs = a_values.[78] &&& 1u
                if rel lhs rhs then // this is the constraint that should hold.
                    ()
                else
                    failwithf "Expected: %d, Obtained: %d\na78.31=%d\na77.31=%d\na74.29=%d\na73.29=%d\nw78.31=%d" lhs rhs (a_values.[78] &&& 1u) ((a_values.[77] <<<< 5) &&& 1u) ((a_values.[74] >>> 2) &&& 1u) ((a_values.[73] >>> 2) &&& 1u) (words.[78] &&& 1u)
                a, b, c, d, e
            | _ ->
                let f, k =
                    if i <= 19 then
                        (b &&& c) ||| ((~~~b) &&& d), 0x5a827999u
                    elif i <= 39 then
                        (b ^^^ c ^^^ d), 0x6ed9eba1u
                    elif i <= 59 then
                        (b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDCu
                    else
                        (b ^^^ c ^^^ d), 0xca62c1d6u
                let temp = (a <<<< 5) + f + e + k + words.[i]
                a_values.[i] <- temp
                spliffle temp a (b <<<< 30) c d (i+1)
        let x0, x1, x2, x3, x4 = spliffle h0 h1 h2 h3 h4 0
        x0, x1, x2, x3, x4
    let compressionResult =
        processChunk (H0, H1, H2, H3, H4) (bytesToHashInput message len)
    compressionResult

let hashString hexInput dwlen =
    let input =
        match hexstringToBytes hexInput with
        | Some x -> x
        | None -> failwithf "'%s' is not a valid hex-string" hexInput
    hash input (int dwlen)

type PreimageCalculator<'T>(repr : IRepresentation<'T>, hexInput, storage : IStorage<'T>, dwlen) =
    do
        if dwlen > 447u then
            // preimage calculation COULD do more; see sha1compress project.
            // But I'm artificially limiting it here, for simplicity's sake.
            failwith "Preimage calculation is artificially limited to single-chunk length (max=447 bits)"
    // first, let's make the hash.
    let c0,c1,c2,c3,c4 = hashString hexInput dwlen
    // now that I have the hash, I can use the representation
    // to create a preimage-version.
    member __.ExpectedOutput = sprintf "%08x%08x%08x%08x%08x" c0 c1 c2 c3 c4
    member __.SingleEquationForm () =
        let mutable x =
            let initial = storage.Get (Utilities.hashDesignator 0)
            if c0.[0] then initial
            else repr.Not initial
        for idx = 1 to 159 do
            let v = match idx/32 with 0->c0 | 1->c1 | 2->c2 | 3->c3 | 4->c4 | _ -> failwith "wtf?! in SingularOutput"
            let key = Utilities.hashDesignator idx
            // get the correct representation from the output.
            let y = storage.Get key
            x <-
                if v.[idx%32] then repr.And x y
                else repr.And x (repr.Not y)
        x