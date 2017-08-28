#time
#load "Dependencies.fsx"
#load "DebugCommon.fs"
#load "AIG.fs"
#load "CNF.fs"
#load "CNF-Tseitin.fs"
#load "BDD.fs"

// screw this - I'm a developer, and this one is important enough to develop.  So, let's do a proper design & implementation.

open FinalEquation
open FinalEquation.CommonStructure
open FinalEquation.CommonStructure.SubCalculations

type InputOutput = { Input : string; Output : string}

let dwlen_map = 
    [|
        // dwlen * (output * input)
        1u, "f27f2f69b2feae700d3a8e5769881c9223f9d42a", "ff"
        2u, "71c10ea23fe185e1eefe7b2dea1bb12cb35d23da", "ff"
        3u, "e3eee297aa09a22655a858cced91f6282bde72ce", "af"
        6u, "261f6b322cb0ca9eabc2ea17d0211af21dd90720", "ac"
        10u, "cf6b04eb0fa6a2cb006507d7b0ae78eeb787726f", "deadbeef"
        16u, "b1fef21c7d8753f899e4ba14268b169b7b451adc", "deadbeef"
        32u, "704a68b8a2d7bed0e6b19d21a8e66702634085fb", "deadbeef"
        64u, "c9176211c8b091deaf915c3720c4e9260e78cf0a", "deadbeefcafeb4be"
        96u, "2c0257f8264910d27729d68ad1ee86d6aa9e3cf3", "deadbeefcafeb4beabad1dea"
        128u, "8d738caaed10771cfebd6067adf9d5759e715989", "deadbeefcafeb4beabad1dea12345678"
        256u, "da2d58e37c2e736bf94056e518e99d3347bdce11", "deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d261f6b327e27c2ad"
    |] |> Array.map (fun (k,o,i) -> k, {Input=i;Output=o})
    |> Map.ofArray

type DescentFunc =
| DescendAlways
| SubstituteForV
| SubstituteForF
/// Only keys above a particular round.  DOES NOT APPLY to w-values!
| AboveRound of int
/// Any will take the first InsteadOf that it is given, and will only descend if all nested funcs agree.
| Any of DescentFunc list
with
    override __.ToString () =
        match __ with
        | DescendAlways -> "descend"
        | SubstituteForV -> "subV"
        | SubstituteForF -> "subF"
        | AboveRound n -> sprintf "geq%02d" n
        | Any xs -> xs |> List.map string |> String.concat "_"

let descend _ _ = Yes

let subs_for_v (key : Designator) (mkVar : unit -> 'a) : SubCalcRecursionResponse<'a> =
    let c0 = key.Var = V.V0 && key.Bit <> 26
    let c1 = key.Var = V.V1 && key.Bit <> 26 && key.Bit <> 25
    if c0 || c1 then InsteadUse (mkVar)
    else Yes

let subs_for_f (key : Designator) (mkVar : unit -> 'a) : SubCalcRecursionResponse<'a> =
    if key.Var = V.F then
        //printfn ":: subs_for_f got %s, returning a new var to use." key.S
        InsteadUse (mkVar)
    else
        //printfn ":: subs_for_f got %s, says YES/DESCEND" key.S
        Yes

let above_round n (key : Designator) (mkVar : unit -> 'a) : SubCalcRecursionResponse<'a> =
    if key.Round > n then
        //printfn ":: above_round(%02d) got %s, says YES/DESCEND" n key.S
        Yes
    else
        //printfn ":: above_round(%02d) got %s, returning a new var to use." n key.S
        InsteadUse (mkVar)

let rec make_descentFunc spec mkVar =
    match spec with
    | DescendAlways -> fun k -> descend k mkVar
    | SubstituteForV -> fun k -> subs_for_v k mkVar
    | SubstituteForF -> fun k -> subs_for_f k mkVar
    | AboveRound n -> fun k -> above_round n k mkVar
    | Any specs ->
        let funcs = specs |> List.map (fun x -> make_descentFunc x mkVar)
        let combinedFunc k =
            let rec combinedFunc fs =
                match fs with
                | [] ->
                    //printfn ":: combined_func verdict is YES/DESCEND"
                    Yes
                | f::fs ->
                    match f k with
                    | Yes -> combinedFunc fs
                    | InsteadUse x ->
                        //printfn ":: combined_func will return a new var to use."
                        InsteadUse x
            combinedFunc funcs
        combinedFunc

let inline generate dwlen mod_dwlen (o : 'a) (r : IRepresentation<'b>) (s : IStorage<'b>) (mkVar : unit -> 'b) write spec =
    let df = make_descentFunc spec mkVar
    let invCalc = InvHashCalculator(dwlen, dwlen_map.[dwlen].Output, r, s, BaseXor, Depends df)
    let out = invCalc.GenerateRepresentation [|0..159|]
    let fn = sprintf @"P:\exp1_%d_%s_%O" dwlen (o.GetType().Name) spec
    write fn out o mod_dwlen

let typical_mkVar dwlen (r : IRepresentation<_>) =
    let v = ref 0
    fun () ->
        let v' = r.MakeVariable(dwlen + uint32 !v)
        v := !v + 1
        v'

let count_extras dwlen spec =
    use o = new Debugging.PassThrough ()
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(dwlen, r) :> IStorage<_>
    let extras = ref 0
    let mkVar () =
        let v = r.MakeVariable(dwlen + uint32 !extras)
        extras := !extras + 1
        v
    let write = fun _ _ _ _ -> uint32 !extras
    generate dwlen dwlen o r s mkVar write spec

let experiment1 dwlen mkRepr write spec =
    let num_extra = count_extras dwlen spec
    printfn "Number of extra vars: %d" num_extra
    let modified_dwlen = dwlen + num_extra
    use o = mkRepr modified_dwlen
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(modified_dwlen, r) :> IStorage<_>
    let mkVar = typical_mkVar dwlen r
    generate dwlen modified_dwlen o r s mkVar write spec

let specs =
    [
        SubstituteForF
        SubstituteForV
        Any [SubstituteForF; SubstituteForV]
        AboveRound 79
        AboveRound 78
        AboveRound 77
        AboveRound 76
        AboveRound 75
        AboveRound 74
        AboveRound 73
        AboveRound 72
        AboveRound 71
        AboveRound 70
        AboveRound 60
        AboveRound 50
        AboveRound 40
        AboveRound 30
        AboveRound 20
        AboveRound 10
        AboveRound 9
        AboveRound 8
        AboveRound 7
        AboveRound 6
        AboveRound 5
        AboveRound 4
        AboveRound 3
        AboveRound 2
        AboveRound 1
        Any [SubstituteForF; AboveRound 79]
        Any [SubstituteForF; AboveRound 78]
        Any [SubstituteForF; AboveRound 77]
        Any [SubstituteForF; AboveRound 76]
        Any [SubstituteForF; AboveRound 75]
        Any [SubstituteForF; AboveRound 74]
        Any [SubstituteForF; AboveRound 73]
        Any [SubstituteForF; AboveRound 72]
        Any [SubstituteForF; AboveRound 71]
        Any [SubstituteForF; AboveRound 70]
        Any [SubstituteForF; AboveRound 60]
        Any [SubstituteForF; AboveRound 50]
        Any [SubstituteForF; AboveRound 40]
        Any [SubstituteForV; AboveRound 78]
        Any [SubstituteForV; AboveRound 77]
        Any [SubstituteForV; AboveRound 76]
        Any [SubstituteForV; AboveRound 75]
        Any [SubstituteForV; AboveRound 74]
        Any [SubstituteForV; AboveRound 73]
        Any [SubstituteForV; AboveRound 72]
        Any [SubstituteForV; AboveRound 71]
        Any [SubstituteForV; AboveRound 70]
        Any [SubstituteForV; AboveRound 60]
        Any [SubstituteForV; AboveRound 50]
        Any [SubstituteForV; AboveRound 40]
        Any [SubstituteForF; SubstituteForV; AboveRound 79]
        Any [SubstituteForF; SubstituteForV; AboveRound 78]
        Any [SubstituteForF; SubstituteForV; AboveRound 77]
        Any [SubstituteForF; SubstituteForV; AboveRound 76]
        Any [SubstituteForF; SubstituteForV; AboveRound 75]
        Any [SubstituteForF; SubstituteForV; AboveRound 74]
        Any [SubstituteForF; SubstituteForV; AboveRound 73]
        Any [SubstituteForF; SubstituteForV; AboveRound 72]
        Any [SubstituteForF; SubstituteForV; AboveRound 71]
        Any [SubstituteForF; SubstituteForV; AboveRound 70]
        Any [SubstituteForF; SubstituteForV; AboveRound 60]
        Any [SubstituteForF; SubstituteForV; AboveRound 50]
        Any [SubstituteForF; SubstituteForV; AboveRound 40]
        DescendAlways
    ]

let mkAIG dwl = new AIG.AndInverterGraph(dwl)
let mkCNF dwl = new CNF.Tseitin.ConjunctiveNormalForm(dwl)
let write_AIG fn out (o : AIG.AndInverterGraph) dwl =
    printfn "%A" o.Stats
    let abc = AIG.ABCInterface(dwl)
    abc.WriteAiger(o.AAG, fn + ".aig")
let write_CNF fn out (o : CNF.Tseitin.ConjunctiveNormalForm) dwl =
    System.IO.File.WriteAllText(fn + ".cnf", o.asDIMACS out)

let write_multiple_files () =
    for spec in specs do
        experiment1 256u mkAIG write_AIG spec
        experiment1 256u mkCNF write_CNF spec

(* // :'( ... these expand far too fast for this to be done! :'-(
experiment1 256u (fun dwl -> new BDD.BinaryDecisionDiagram(dwl))
    (fun fn out o dwl -> if not <| o.WriteDot (fn + ".dot") [|"Final out", out|] then printfn "Failed to write dotfile :-( : %s" fn)
    (IfAllAgree [SubstituteForF; SubstituteForV; AboveRound 78])
experiment1 (fun dwl -> new BDD.BinaryDecisionDiagram(dwl))
    (fun (fn,out,o,dwl) -> if not <| o.WriteDot (fn + ".dot") [|"Final out", out|] then printfn "Failed to write dotfile :-( : %s" fn)
    "carries_f_to_var"
*)
