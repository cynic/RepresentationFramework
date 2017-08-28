#load "Dependencies.fsx"
#load "BDD.fs"
#r "bin/Release/MathNet.Numerics.dll"
#r "bin/Release/MathNet.Numerics.FSharp.dll"

open FinalEquation
open FinalEquation.CommonStructure
open FinalEquation.CommonStructure.SubCalculations
open FinalEquation.BDD
open MathNet.Numerics.Statistics

let testInput =
    [|
        "deadbeef"; "cafebabe"; "abad1dea"; "b33fd00d"
        "01234567"; "89abcdef"; "0f1e2d3c"; "4b5a6978"
        "b01dface"; "deadbea7"; "5ca1ab1e"; "cab005e5"
        "0b501e7e"; "acc01ade"
    |] |> String.concat ""

let thesisExampleBDD () =
    use o = new BinaryDecisionDiagram(4u, Reordering.None)
    let r = o :> IRepresentation<_>
    let d = r.MakeVariable 3u
    let c = r.MakeVariable 2u
    let b = r.MakeVariable 1u
    let a = r.MakeVariable 0u
    let result = r.Or d (r.And b (r.Or a c))
    o.WriteDot @"P:\bdd_thesis_example.dot" [|"Final output", result|]

let string_of_method = function
    | Reordering.Exact -> "Exact"
    | Reordering.GeneticAlgorithm -> "Genetic"
    | Reordering.GroupSift -> "GroupSift"
    | Reordering.GroupSiftConverge -> "\"GroupSift (iter.)\""
    | Reordering.LazySift -> "LazySift"
    | Reordering.None -> "None"
    | Reordering.RandomPivoting -> "RandomPivot"
    | Reordering.RandomSwaps -> "RandomSwaps"
    | Reordering.Sift -> "Sift"
    | Reordering.SiftConverge -> "SiftConverge"
    | Reordering.SiftSymmetric -> "SiftSymmetric"
    | Reordering.SiftSymmetricConverge -> "\"SiftSymmetric (iter.)\""
    | Reordering.SimulatedAnnealing -> "SimulatedAnnealing"
    | Reordering.WindowSize2 -> "\"Window (sz=2)\""
    | Reordering.WindowSize3 -> "\"Window (sz=3)\""
    | Reordering.WindowSize4 -> "\"Window (sz=4)\""
    | Reordering.WindowSize2Converge -> "\"Window (sz=2, iter.)\""
    | Reordering.WindowSize3Converge -> "\"Window (sz=3, iter.)\""
    | Reordering.WindowSize4Converge -> "\"Window (sz=4, iter.)\""
    | x -> failwithf "Unknown reordering method for BDDs: %d" x

let trackStats dwlen reorderMethod =
    use o = new BinaryDecisionDiagram(dwlen, reorderMethod)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage<_>(dwlen) :> IStorage<_>
    let w = Words.Traditional(dwlen, r, s)
    let sc = SubCalculations.AndOrXorNot(dwlen, w, Never, r, s)
    let h = HashCalculator<_>(dwlen, r, s, sc)

    let timer = System.Diagnostics.Stopwatch()
    timer.Start ()
    h.GenerateRepresentation ()
    timer.Stop ()
    let roots = [|0..159|] |> Array.map (Utilities.hashDesignator dwlen >> s.Get)
    let totalCount = o.NodeCount roots

    let write what (data : float[]) =
        let stat = Statistics.FiveNumberSummary data
        let geomean =
            let geomean = Statistics.GeometricMean data
            if System.Double.IsNaN geomean then "?" else sprintf "%f" geomean
        match what with
        | "combined" ->
            let ordering = o.ReorderStats.NodeOrdering |> Seq.map string |> String.concat "-"
            printfn "Node ordering: %s" ordering
            System.IO.File.AppendAllText(@"P:\bdd_reorder_stats_combined.dat",
                sprintf "%d %s %f %f %f %f %f %s %s %d %d\n" dwlen (string_of_method reorderMethod) stat.[0] stat.[1] stat.[2] stat.[3] stat.[4] geomean ordering timer.ElapsedMilliseconds totalCount
            )
            System.IO.File.AppendAllText(sprintf @"P:\bdd_reorder_rm%02d.dat" reorderMethod,
                sprintf "%d %s %f %f %f %f %f %s %s %d %d\n" dwlen (string_of_method reorderMethod) stat.[0] stat.[1] stat.[2] stat.[3] stat.[4] geomean ordering timer.ElapsedMilliseconds totalCount
            )
        | _ ->
            System.IO.File.AppendAllText(sprintf @"P:\bdd_reorder_stats_%s.dat" what,
                sprintf "%d %s %f %f %f %f %f %s\n" dwlen (string_of_method reorderMethod) stat.[0] stat.[1] stat.[2] stat.[3] stat.[4] geomean
            )
            System.IO.File.AppendAllText(sprintf @"P:\bdd_reorder_rm%02d_%s.dat" reorderMethod what,
                sprintf "%d %s %f %f %f %f %f %s\n" dwlen (string_of_method reorderMethod) stat.[0] stat.[1] stat.[2] stat.[3] stat.[4] geomean
            )

    let data = o.ReorderStats
    write "and" data.AndTimesMS
    write "or" data.OrTimesMS
    write "xor" data.XorTimesMS
    write "combined" (Array.concat [data.AndTimesMS ; data.OrTimesMS ; data.XorTimesMS])
    printfn "[%02d] %s : %dms" dwlen (string_of_method reorderMethod) timer.ElapsedMilliseconds

    // ...and, just for fun ...

    let finalBits =
        [|0..(int dwlen-1)/2|] |> Array.map (fun n ->
            let key = Utilities.hashDesignator dwlen n
            let value = s.[key]
            sprintf "%d,%d" key.Round key.Bit, value
        )
    o.WriteDot (sprintf @"P:\bdd_%02d_rm%02d.dot" dwlen reorderMethod) finalBits |> ignore

    // ...right, fun over!

    timer.ElapsedMilliseconds

let generateStats () =
    let initialMethods = [Reordering.Exact; Reordering.GeneticAlgorithm; Reordering.GroupSift; Reordering.GroupSiftConverge; Reordering.LazySift; Reordering.None; Reordering.RandomPivoting; Reordering.RandomSwaps; Reordering.Sift; Reordering.SiftConverge; Reordering.SiftSymmetric; Reordering.SiftSymmetricConverge; Reordering.SimulatedAnnealing; Reordering.WindowSize2; Reordering.WindowSize3; Reordering.WindowSize4; Reordering.WindowSize2Converge; Reordering.WindowSize3Converge; Reordering.WindowSize4Converge]
    let rec doStats dwlen methods_todo methods_next =
        match dwlen with
        | 20u -> () // done!
        | _ ->
            match methods_todo with
            | [] ->
                printfn "Methods remaining: %A" methods_next
                doStats (dwlen+1u) methods_next []
            | x::xs ->
                // Reordering.None, and dwlen=4, causes an unmanaged code snafu - CUDD's fault, not mine? :-/.  So, avoid that explicitly.
                if x = Reordering.None && dwlen = 4u then
                    // DO NOTHING, and exclude .None from consideration for the future.
                    printfn "Special case: excluding combination of dwlen=4, reordering=none"
                    doStats dwlen xs methods_next
                else
                    // this is the non-special-cased functionality :D.
                    let time_taken_ms = trackStats dwlen x
                    if time_taken_ms > 2L*60L*1000L then // i.e., 2 minutes
                        printfn "Excluding method: %s" (string_of_method x)
                        doStats dwlen xs methods_next
                    else
                        doStats dwlen xs (x::methods_next)
    doStats 1u initialMethods []

// w_method makes no difference whatsoever; BDD is a canonical form.

let makeBdd dwlen =
    use o = new BinaryDecisionDiagram(dwlen)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage<_>(dwlen) :> IStorage<_>
    let w = FinalEquation.Words.Traditional(dwlen, r, s)
    let sc = SubCalculations.AndOrXorNot(dwlen, w, Never, r, s)
    let h = HashCalculator<_>(dwlen, r, s, sc)

    h.GenerateRepresentation ()

    let fn = sprintf @"P:\bdd_%d-m.dot" dwlen // m = multi-output

    let finalBits =
        [|0..(int dwlen-1)/2|] |> Array.map (fun n ->
            let key = Utilities.hashDesignator dwlen n
            let value = s.[key]
            sprintf "%d,%d" key.Round key.Bit, value
        )
    ignore <| o.WriteDot fn finalBits

    let firstBit = s.[Utilities.hashDesignator dwlen 0]
    let fn = sprintf @"P:\bdd_%d-s.dot" dwlen // s = single-output
    ignore <| o.WriteDot fn [|"80,27",firstBit|]

    let pre = PreimageCalculator(r, testInput, s, dwlen)

    let fn = sprintf @"P:\bdd_%02d-pre.dot" dwlen
    o.PrintCountAfterOps <- true
    let sef = pre.SingleEquationForm ()
    o.PrintCountAfterOps <- false
    let to_write = [|"Final output", sef|]

    if o.WriteDot fn to_write then
        printfn "%s written." fn
    else printfn "ERROR, could not write %s :-(" fn



let make_preimage_bdd wb (o : BinaryDecisionDiagram) (hashBits : _[]) s dwlen =
    // this will create vars for 79..75 as well.
    //let dwlen = 6u*32u // = 192
    let r = o :> IRepresentation<_>
    let words = Words.BaseXor(dwlen, r, s) :> IWords<_>
    let sc = XorAnd(dwlen, words, Never, r, s) :> ISubCalculator<_>
    let designator_to_variable_map = System.Collections.Generic.Dictionary()
    let (~%) designator =
        s.GetOrGenerate designator (fun d ->
            if d.Var=V.A && d.Round >= 76 then
                let oBit = hashBits.[Utilities.hashDesignatorInv d]
                if oBit then r.Constants.One else r.Constants.Zero
            else
                let b = r.MakeVariable(!wb)
                printfn "%O ---> %d" designator !wb
                designator_to_variable_map.[designator] <- b
                wb := !wb + 1u
                b
        )
    let mutable current = Unchecked.defaultof<int64<node>>
    let getW x =
        // sc.W x
        %x
    Array.append [|26..-1..0|] [|31..-1..27|]
    |> Array.iter (fun i ->
        let t = Designator(dwlen, 80, i, V.A)
        let k = if Utilities.kbit t then r.Constants.One else r.Constants.Zero
        if i=26 then
            // there's no v0, there's no v1.
            let a,f,e,w,_,_ = Keys.inputKeys_overall t
            let b,c,d = Keys.inputKeys_f f
            s.Store f (r.Xor %b %c |> r.Xor %d)
            let result = r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (getW w) |> r.Xor k
            if hashBits.[Utilities.hashDesignatorInv t] then
                current <- result
            else
                current <- r.Not result

        elif i=25 then
            // there is a v0, but no v1.
            let a,f,e,w,v0,_ = Keys.inputKeys_overall t
            let b,c,d = Keys.inputKeys_f f
            s.Store f (r.Xor %b %c |> r.Xor %d)
            let v0 = sc.V0(Option.get v0)
            let result = r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (getW w) |> r.Xor v0 |> r.Xor k
            if hashBits.[Utilities.hashDesignatorInv t] then
                current <- r.And current result
            else
                current <- r.And current (r.Not result)
        else
            // both a v0 and a v1
            let a,f,e,w,v0,v1 = Keys.inputKeys_overall t
            let b,c,d = Keys.inputKeys_f f
            s.Store f (r.Xor %b %c |> r.Xor %d)
            let v0 = sc.V0(Option.get v0)
            let v1 = sc.V1(Option.get v1)
            let result = r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (getW w) |> r.Xor v0 |> r.Xor v1 |> r.Xor k
            if hashBits.[Utilities.hashDesignatorInv t] then
                current <- r.And current result
            else
                current <- r.And current (r.Not result)
        let sz = o.NodeCount [current]
        printfn "i=%d, BDD nodecount = %d" i sz
        o.WriteDot (sprintf @"P:\bdd_preimage_%d_%d.dot" i dwlen) [|"combined", current|] |> ignore
    )
    current, designator_to_variable_map

let make_a_bdds dwlen wb (o : BinaryDecisionDiagram) (s : IStorage<_>) p =
    //let dwlen = 6u*32u // = 192
    let r = o :> IRepresentation<_>
    let words =
        //Words.Dummy()
        Words.BaseXor(dwlen, r, s) :> IWords<_>
    let sc = XorAnd(dwlen, words, Never, r, s) :> ISubCalculator<_>
    let designator_to_variable_map = System.Collections.Generic.Dictionary()
    let (~%) designator =
        s.GetOrGenerate designator (fun d ->
            let b = r.MakeVariable(!wb)
            printfn "%O ---> %d" designator !wb
            designator_to_variable_map.[designator] <- b
            wb := !wb + 1u
            b
        )
    let outputs =
        Array.append [|26..-1..0|] [|31..-1..27|]
        |> Array.map (fun i ->
            let t = Designator(dwlen, p, i, V.A)
            let bdd =
                if i=26 then
                    // there's no v0, there's no v1.
                    let a,f,e,w,_,_ = Keys.inputKeys_overall t
                    let b,c,d = Keys.inputKeys_f f
                    s.Store f (r.Xor %b %c |> r.Xor %d)
                    r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (sc.W w)
                elif i=25 then
                    // there is a v0, but no v1.
                    let a,f,e,w,v0,_ = Keys.inputKeys_overall t
                    let b,c,d = Keys.inputKeys_f f
                    s.Store f (r.Xor %b %c |> r.Xor %d)
                    let v0 = sc.V0(Option.get v0)
                    r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (sc.W w) |> r.Xor v0
                else
                    // both a v0 and a v1
                    let a,f,e,w,v0,v1 = Keys.inputKeys_overall t
                    let b,c,d = Keys.inputKeys_f f
                    s.Store f (r.Xor %b %c |> r.Xor %d)
                    let v0 = sc.V0(Option.get v0)
                    let v1 = sc.V1(Option.get v1)
                    r.Xor %a %b |> r.Xor %c |> r.Xor %d |> r.Xor %e |> r.Xor (sc.W w) |> r.Xor v0 |> r.Xor v1
            s.Store t (if Utilities.kbit t then r.Not bdd else bdd)
            let sz = o.NodeCount [s.[t]]
            printfn "i=%d, BDD nodecount = %d" i sz
            o.WriteDot (sprintf @"P:\bdd_%d_%d_individual.dot" p i) [|sprintf "a(%d,%d)" p i, s.[t]|] |> ignore
            i, s.[t]
        )
    outputs, designator_to_variable_map

let dwlen = 256u
let storage = Storage.MemoryStorage<_>() :> IStorage<_>
// related input data for this hash is: deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d261f6b327e27c2ad
let hashString = "da2d58e37c2e736bf94056e518e99d3347bdce11"
let hashBits = Utilities.hashToBits hashString |> Seq.toArray
// this variable is used to keep auto-incrementing vars through the function calls.
let wb = ref 0u
// this is the object underneath the representation.
let bdd_o = new BinaryDecisionDiagram(2560u * 6u)
let repr = bdd_o :> IRepresentation<_>
// put in the constants.
SubCalculations.Internal.init_subcalc_constants dwlen storage repr
// the call to make_preimage_bdd will give back a BDD, AND a designator-to-variable-map.
// No variables for r=80..76 exist, because they have been replaced by constants.
// The designator-to-variable map here refers to variables from r=75.
let make_preimage_result = make_preimage_bdd wb bdd_o hashBits storage dwlen
let mutable preimage_bdd = fst make_preimage_result
let designator_to_var_map = snd make_preimage_result
// now, put in a "random" number for r=75.  For now, the "random" number is
// actually going to be the "real" preimage number, because I want to check that
// this thing works on a structural level.
(*
Round 71, a=0554081b 
Round 72, a=4c0310b6 
Round 73, a=7e498aeb 
Round 74, a=07508755 
Round 75, a=7a95aab2 <-- this one here.  Am I making a rotation error?  Not 100% sure.
Round 76, a=1ef73845 
Round 77, a=63a674cc 
Round 78, a=e5015b97 
Round 79, a=7c2e736b 
Round 80, a=da2d58e3 
*)
let a75_value = 0x7a95aab2u
// now, put that into the r=75 variables.
for i = 0 to 31 do
    let d = Designator(dwlen, 75, i, V.A)
    let bdd_var = // this is the linked BDD variable.
        designator_to_var_map.[d]
    // now, if this bit is "true", then AND by it, and update the ROBDD.
    if a75_value.[i] then preimage_bdd <- repr.And preimage_bdd bdd_var
    // otherwise, AND by its complement.
    else preimage_bdd <- repr.And preimage_bdd (repr.Not bdd_var)

// let's write out a diagram.
bdd_o.WriteDot @"P:\preimage_bdd.dot" [|"combined, with 75", preimage_bdd|]

// now I want to make two sets of things: a set of w-equations and a set of a-equations.
// TODO - let me see the generated DOTfile first....
// Seen!  OK, it's as I expect: a long, continuous line that goes downwards.
// Now, that line contains both a-values and w-values.  Let's look into it.
// first, I will need an inverse of designator_to_var_map, because I am looking at NODEs
// and wanting DESIGNATORs
let var_to_designator =
    let result = System.Collections.Generic.Dictionary(designator_to_var_map.Count)
    for kvp in designator_to_var_map do
        result.Add(kvp.Value, kvp.Key) // .Add will throw an exception on duplicate key, which is good.
    result
// I'll be expanding words, so I'll want a set of expanded words.
let w_eqn (d : Designator) =
    let constants, variables = Words.can_affect d.Round d.Bit |> Array.partition (fun i -> i >= int dwlen)
    // the 'constants' will end up telling us whether or not to invert the 'result'.
    // let's say that our equation is a + b + c = 1 (where the '1' comes from the BDD)
    // Now, on the LHS, there's also a constant-1 result.  So it's actually
    // a + b + c + 1 = 1
    // Which works out to being the same as
    // a + b + c = 0
    // Because we can subtract that 1 from both sides.
    let eqnResult = Array.zeroCreate (int dwlen)
    for v in variables do
        eqnResult.[v] <- 1
    let constResult =
        match constants |> Array.map (Words.constantValue dwlen) with
        | [||] | [|false|] -> false
        | [|true|] -> true
        | xs -> (Seq.filter ((=) true) xs |> Seq.length) % 2 = 1
    eqnResult, constResult
let a_eqn (d : Designator) =
    // this is going to be afewv0v1.
let rec populate_sets (curNode : Node) seeking a_set w_set =
    match curNode.Value with
    | One | Zero -> a_set, w_set // we are done!
    | Opaque curValue ->
        let seeking = if curNode.IsComplemented then not seeking else seeking
        match curNode.ThenChild.Value, curNode.ElseChild.Value with
        | Opaque _, Opaque _ -> failwith "Two opaque nodes found - should be impossible!"
        | Opaque _, (One|Zero) ->
            match var_to_designator.TryGetValue curValue with
            | false, _ -> populate_sets seeking curNode.ThenChild a_set w_set // push down.
            | true, designator ->
                if designator.Var = V.W then
                    let w_eqn, w_const = w_eqn (designator.Round*32+designator.Bit)
                    if w_const then // since this is the THEN child, the actual must be 0 - see comment in w_eqn
                        populate_sets curNode.ThenChild seeking a_set ((w_eqn, 0uy)::w_set)
                    else // actual must be 1, because this is the THEN child.
                        populate_sets curNode.ThenChild seeking a_set ((w_eqn, 1uy)::w_set)
                else // must be V.A
                    let a_eqn, a_const = a_eqn designator
        | One, Zero ->
            // both lead to a terminal?  But which one is the right one?

// now, make 2560 BDDs.

let bdd_array = Array.init 76 (fun n ->
    // make the row.  HOWEVER, this will give me the row in the order 26..0,31..27.
    // I want the row in the order 0..31, so that bdd_array.[r].[i] and Designator(_,r,i,V.A)
    // map to each other.
    let arr = make_a_bdds dwlen bdd_o storage (n + 1)
    arr |> Array.sortBy fst |> Array.map snd
)
// so: bdd_array.[r].[i] will give me the BDD for that (r,i) combination.


(*

type WBox (target_designator : Designator) = // each WBox actually represents an a-value...
    let xorCount = Array.zeroCreate 512 // a 512-length array, containing the xorcount for every $w$-value.
    let mutable oneCount = 0
    member __.XorCount with get () = xorCount
    member __.BumpXorCount x = xorCount.[x] <- xorCount.[x] + 1
    member __.BumpXorCount (r,i) = xorCount.[r*32+i] <- xorCount.[r*32+i] + 1
    member __.BumpOneCount () = oneCount <- oneCount + 1
    member __.TargetDesignator with get () = target_designator
    member __.OneCount with get () = oneCount
    member __.XorWith (x : WBox) =
        for i = 0 to 511 do
            xorCount.[i] <- xorCount.[i] + x.XorCount.[i]
        oneCount <- oneCount + x.OneCount
    member __.WMembers
        with get () =
            seq {
                for i = 0 to 511 do
                    if xorCount.[i] % 2 = 1 then yield Designator(target_designator.DWLen, i/32, i%32, V.W)
            }

type Remaining =
| ABCDKEWV0V1 of Designator // at this point, nothing has been done.  I can make a WBox from W and K.
| ABCDEV0V1 of WBox // I can work down through the E values.
| ABCDV0V1 of WBox // I can work down through the A values.
| BCDV0V1 of WBox // I should be able to work through BCD, either directly, or with a BDD?
| V0V1 of WBox // Same holds for V0 and V1
| Complete of WBox

let make_remaining dwlen = Array.init (81*32) (fun i -> ABCDKEWV0V1 <| { Round=i/32; Bit=i%32; Var=V.A })

let work_out dwlen (remaining : Remaining[]) =
    let storage = Storage.MemoryStorage() :> IStorage<_>
    storage.StoreINE ({ Round=0; Bit=i; Var=V.A }) (0xe8a4602cu.[i])
    storage.StoreINE ({ Round=-1; Bit=i; Var=V.A }) (0xf9b5713du.[i])
    storage.StoreINE ({ Round=-2; Bit=i; Var=V.A }) (0x5d6e7f4cu.[i])
    storage.StoreINE ({ Round=-3; Bit=i; Var=V.A }) (0x192a3b08u.[i])
    storage.StoreINE ({ Round=-4; Bit=i; Var=V.A }) (0xe970f861u.[i])
    storage.StoreINE ({ Round=0; Bit=i; Var=V.F }) (0x98badcfeu.[i])
    storage.StoreINE ({ Round=1; Bit=i; Var=V.F }) (0xfbfbfefeu.[i])
    let rec descend (extract_keys : _ -> Designator * Designator) target_key (wbox : WBox) =
        if storage.Exists target_key then // yay, it's a constant
            if storage.[target_key] then wbox.BumpOneCount ()
            wbox
        else
            // get the $w$ value that is part of this $a$/$e$-value.
            let target_a,_,target_e,wKey,_,_ = Keys.inputKeys_overall target_key
            for v in Words.Internal.can_affect wKey.Round wKey.Bit do
                wbox.BumpXorCount v
            if Utilities.kbit target_key then wbox.BumpOneCount ()
            descend target_a wbox // keep going down the chain.
            descend target_e wbox // keep going down the chain.
    let rec work_out specific =
        match specific with
        | ABCDKEWV0V1 d ->
            let wbox = WBox(d)
            if Utilities.kbit d then wbox.BumpOneCount ()
            // ok, that takes care of the K.
            // now, for the W.
            let _,_,_,wKey,_,_ = Keys.inputKeys_overall d
            for flatIdx in Words.Internal.can_affect wKey.Round wKey.Bit do
                wbox.BumpXorCount flatIdx
            // right!  K done, and W done.  Give back the result.
            ABCDEV0V1 wbox
        | ABCDEV0V1 wbox ->
            // OK, I want to handle the E value here.  
            // keep going to lower and lower levels, XOR'ing with the $e$-values encountered as we go.
            let extract_key (_,_,e,w,_,_) = e,w
            let _,_,target_e,_,_,_ = Keys.inputKeys_overall wbox.TargetDesignator
            ABCDV0V1 (descend extract_key target_e wbox)
        | ABCDV0V1 wbox ->
            // OK, I want to handle the A value here.  
            // keep going to lower and lower levels, XOR'ing with the $a$-values encountered as we go.
            let extract_key (a,_,_,w,_,_) = a,w
            let target_a,_,_,_,_,_ = Keys.inputKeys_overall wbox.TargetDesignator
            BCDV0V1 (descend extract_key target_a wbox)
*)                    
(*
(*
    To generate the BDD carry example, I downloaded PBL https://github.com/tyler-utah/PBL and PBDD https://github.com/tyler-utah/PBDD.
    Fixed them up, then ran PBDD with the following script.  After that, it was straight-up editing with vim of the dotfile, and then =>SVG.

    Why?  Because I wanted a ROBDD, not a CBDD.
*)
Var_Order : x1 x2 x3 x4 x5 x6

sub00 = x1 & x2 & x3 & x4 & x5 & ~x6
sub01 = x1 & x2 & x3 & x4 & x5 & x6
sub02 = x1 & x2 & x3 & x4 & ~x5 & x6
sub03 = x1 & x2 & x3 & ~x4 & x5 & x6
sub04 = x1 & x2 & ~x3 & x4 & x5 & x6
sub05 = x1 & ~x2 & x3 & x4 & x5 & x6
sub06 = ~x1 & x2 & x3 & x4 & x5 & x6
sub07 = x1 & x2 & ~x3 & ~x4 & ~x5 & ~x6
sub08 = x1 & ~x2 & x3 & ~x4 & ~x5 & ~x6
sub09 = ~x1 & x2 & x3 & ~x4 & ~x5 & ~x6
sub10 = x1 & ~x2 & ~x3 & x4 & ~x5 & ~x6
sub11 = ~x1 & x2 & ~x3 & x4 & ~x5 & ~x6
sub12 = ~x1 & ~x2 & x3 & x4 & ~x5 & ~x6
sub13 = ~x1 & ~x2 & x3 & x4 & ~x5 & ~x6
sub14 = x1 & ~x2 & ~x3 & ~x4 & x5 & ~x6
sub15 = ~x1 & x2 & ~x3 & ~x4 & x5 & ~x6
sub16 = ~x1 & ~x2 & x3 & ~x4 & x5 & ~x6
sub17 = ~x1 & ~x2 & ~x3 & x4 & x5 & ~x6
sub18 = x1 & ~x2 & ~x3 & ~x4 & ~x5 & x6
sub19 = ~x1 & x2 & ~x3 & ~x4 & ~x5 & x6
sub20 = ~x1 & ~x2 & x3 & ~x4 & ~x5 & x6
sub21 = ~x1 & ~x2 & ~x3 & x4 & ~x5 & x6
sub22 = x1 & ~x2 & ~x3 & ~x4 & ~x5 & ~x6
sub23 = ~x1 & x2 & ~x3 & ~x4 & ~x5 & ~x6
sub24 = ~x1 & ~x2 & x3 & ~x4 & ~x5 & ~x6
sub25 = ~x1 & ~x2 & ~x3 & ~x4 & x5 & ~x6
sub26 = ~x1 & ~x2 & ~x3 & ~x4 & x5 & x6
sub27 = ~x1 & ~x2 & ~x3 & ~x4 & ~x5 & x6

Main_Exp : sub00 | sub01 | sub02 | sub03 | sub04 | sub05 | sub06 | sub07 | sub08 | sub09 | sub10 | sub11 | sub12 | sub13 | sub14 | sub15 | sub16 | sub17 | sub18 | sub19 | sub20 | sub21 | sub22 | sub23 | sub24 | sub25 | sub26 | sub27
*)