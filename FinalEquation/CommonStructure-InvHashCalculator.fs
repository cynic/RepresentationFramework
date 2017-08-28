[<AutoOpen>]
module FinalEquation.CommonStructure.InvHashCalculation

open FinalEquation.CommonStructure.SubCalculations
open FinalEquation.CommonStructure.Verification

/// The hex_hash is the 160-bit hex output (i.e. 20 hex-digits) of the COMPRESSION FUNCTION proper, i.e. **BEFORE D-M STEP**!
/// The sha1compress tool will create these hash values for you.
type InvHashCalculator<'T>(expected_dwlen : uint32, hex_hash : string, repr : IRepresentation<'T>, storage : IStorage<'T>, subcalcs : ISubCalculator<'T>) =
    let hash_bits = Utilities.hashToBits hex_hash |> Seq.toArray
    let desired_outputs =
        [|0..159|]
        |> Array.map (fun v ->
            let key = Utilities.hashDesignator v
            key.Round, key.Bit
        )
    let output_lookup = Array.zip (desired_outputs |> Array.map (fun (p,i) -> p*32+i)) hash_bits |> Map.ofArray
    
    //let subcalc = SubCalculations(expected_dwlen, w, defaultArg subCalcRecursion Always, repr, storage)

    let generate_representation indices =
        // generate all the necessary words.
        // now, need to join the desired_outputs together to find a preimage.
        let break_it_down (r,i) =
            let target = { Round=r; Bit=i; Var=V.A }
        (*
            do
                let a,f,e,w,v0,v1 = // just for printing out!
                    Keys.inputKeys_overall target
                printfn "*** Top-level, seeking: %s = %s ⊕ %s ⊕ %s ⊕ %s ⊕ %s ⊕ %s" target.S a.S f.S e.S w.S v0.S v1.S
        *)
            let pos_a =
                let v = subcalcs.[target]
                match output_lookup.TryFind (r * 32 + i) with
                | Some true -> Some v
                | Some false -> Some (repr.Not v)
                | None -> failwith "IMPOSSIBRU"
            //printfn "*** Top-level, assigning: %s.  (=%c according to hash)" target.S (if output_lookup.[r*32+i] then '1' else '0')
            //storage.Store target a
            pos_a
        let ok_indices = Set.ofArray indices
        desired_outputs
        |> Seq.mapi (fun i v -> i,v)
        |> Seq.filter (fun (i,_) -> Set.contains i ok_indices)
        |> Seq.map snd
        |> Seq.fold (fun state v ->
            match state, break_it_down v with
            | None, x ->
                //printfn "Initial creation"
                x
            | Some state, Some knownVal ->
                //printfn "ANDing %A and %A" state knownVal
                Some (repr.And state knownVal)
             | x, None -> failwith "In generate_representation, I shouldn't be here.........."
            //printfn "Generated, ANDed, value for: %A" v
        ) None
        |> Option.get

    member __.GenerateRepresentation indices =
        generate_representation indices
    member __.VerifyRepresentation () = verify expected_dwlen repr storage 76