//#load "Dependencies.fsx"
#load "CommonStructure-Data.fs"
#load "Words.fs"
#load "CommonStructure-Utilities.fs"
#time
open FinalEquation
open FinalEquation.CommonStructure
open FinalEquation.Words

// let's model a domain store.
type IDomainStore =
    // given a round and an index, a domain store should be able to tell me what the remaining Domain is
    abstract Domain : int -> int -> Set<int>
    // given a round and an index, give me the initial (lower,upper) set bounds for that combination.
    abstract InitialSetBounds : int -> int -> (int * int)
    // change bounds for a given (r,i)
    abstract ChangeBounds : int -> int -> Set<int> -> unit
    // We should be able to remove a possibilty from a constraint store, and provide a reason for that removal.

let init_state_from_bounds f n =
    let lower, upper = f (n/32) (n%32)
    Set.ofSeq {lower..upper}

let f_domain f_key (db : IDomainStore) =
    assert (f_key.Round > 1) // because otherwise, it would be a constant value.
    let bKey, cKey, dKey = Keys.inputKeys_f f_key
    let b, c, d = db.Domain bKey.Round bKey.Bit, db.Domain cKey.Round cKey.Bit, db.Domain dKey.Round dKey.Bit
    let inline isConstant s = Set.count s = 1
    let inline isTrue s = s = Set.singleton 1
    let inline defaultSet () = Set.ofArray [|0;1|]
    if (f_key.Round >= 20 && f_key.Round < 40) || f_key.Round >= 60 then
        match isConstant b, isConstant c, isConstant d with
        | true, true, true ->
            match isTrue b, isTrue c, isTrue d with
            | false, false, true | false, true, false | true, false, false | true, true, true -> Set.singleton 1
            | _ -> Set.singleton 0
        | _ -> defaultSet ()
    elif f_key.Round >= 40 && f_key.Round < 60 then
        // MAJ
        match isConstant b, isConstant c, isConstant d with
        | false, false, false | false, false, true | false, true, false | true, false, false -> defaultSet ()
        | false, true, true ->
            match isTrue c, isTrue d with
            | false, false -> Set.singleton 0
            | false, true | true, false -> defaultSet ()
            | true, true -> Set.singleton 1
        | true, false, true ->
            match isTrue b, isTrue d with
            | false, false -> Set.singleton 0
            | false, true | true, false -> defaultSet ()
            | true, true -> Set.singleton 1
        | true, true, false ->
            match isTrue b, isTrue c with
            | false, false -> Set.singleton 0
            | false, true | true, false -> defaultSet ()
            | true, true -> Set.singleton 1
        | true, true, true ->
            match isTrue b, isTrue c, isTrue d with
            | false, true, true | true, false, true | true, true, false | true, true, true -> Set.singleton 1
            | _ -> Set.singleton 0
    else
        // CHOICE
        match isConstant b, isConstant c, isConstant d with
        | false, false, _ | false, _, false | _, false, false -> defaultSet ()
        | false, true, true ->
            match isTrue c, isTrue d with
            | false, false -> Set.singleton 0
            | false, true | true, false -> defaultSet ()
            | true, true -> Set.singleton 1
        | true, false, true ->
            match isTrue b, isTrue d with
            | false, false -> Set.singleton 0
            | false, true -> Set.singleton 1
            | true, _  -> defaultSet ()
        | true, true, false ->
            match isTrue b, isTrue c with
            | false, _ -> defaultSet ()
            | true, false -> Set.singleton 0
            | true, true -> Set.singleton 1
        | true, true, true ->
            match isTrue b, isTrue c, isTrue d with
            | false, _, false | true, false, _ -> Set.singleton 0
            | false, _, true | true, true, _ -> Set.singleton 1

// # = Set.singleton #
// g = {0..1}
// h = {0..2}
// i = {0..3}
// j = {0..4}
// k = {0..5}
// l = {0..6}
// m = {0..7}
// n = {1..2}
// o = {1..3}
// p = {1..4}
// q = {1..5}
// r = {1..6}
// s = {1..7}
// t = {2..3}
// u = {2..4}
// v = {2..5}
// x = {2..6}
// y = {2..7}
// G = {3..4}
// H = {3..5}
// I = {3..6}
// J = {3..7}
// K = {4..5}
// L = {4..6}
// M = {4..7}
// N = {5..6}
// O = {5..7}
// P = {6..7}
let pp_state (state : _[]) =
    for r = 0 to (state.Length-1)/32 do
        for i = 0 to 31 do
            let s = state.[r*32+i]
            if Set.count s = 1 then printf "%d" (Seq.head s)
            else
                let c =
                    if s = Set.ofList [0..7] then 'h'
                    elif s = Set.ofList [1..7] then 'i'
                    elif s = Set.ofList [2..7] then 'j'
                    elif s = Set.ofList [3..7] then 'k'
                    elif s = Set.ofList [4..7] then 'm'
                    elif s = Set.ofList [5..7] then 'n'
                    elif s = Set.ofList [6..7] then 'o'
                    elif s = Set.ofList [0..6] then 'p'
                    elif s = Set.ofList [1..6] then 'q'
                    elif s = Set.ofList [2..6] then 'r'
                    elif s = Set.ofList [3..6] then 's'
                    elif s = Set.ofList [4..6] then 't'
                    elif s = Set.ofList [5..6] then 'u'
                    elif s = Set.ofList [0..5] then 'v'
                    elif s = Set.ofList [1..5] then 'x'
                    elif s = Set.ofList [2..5] then 'y'
                    elif s = Set.ofList [3..5] then 'z'
                    elif s = Set.ofList [4..5] then 'H'
                    elif s = Set.ofList [0..4] then 'J'
                    elif s = Set.ofList [1..4] then 'K'
                    elif s = Set.ofList [2..4] then 'L'
                    elif s = Set.ofList [3..4] then 'M'
                    elif s = Set.ofList [0..3] then 'N'
                    elif s = Set.ofList [1..3] then 'O'
                    elif s = Set.ofList [2..3] then 'P'
                    elif s = Set.ofList [0..2] then 'Q'
                    elif s = Set.ofList [1..2] then 'R'
                    elif s = Set.ofList [0..1] then 'S'
                    else failwithf "Unexpected state: %A" s
                printf "%c" c
        printfn " ~~ %02d" r

type ADomainStore(hashstring) as __ =
    static let initialDomain = Set.ofArray [|0;1|]
    let preimageBits = Utilities.hashToBits hashstring |> Seq.toArray
    let initialSetBounds r i =
        if r = 0 then (if 0xe8a4602cu.[i] then 1,1 else 0,0)
        elif r >= 76 && r <= 80 then
            let bitIdx = Utilities.hashDesignatorInv <| { Round=r; Bit=i; Var=V.A }
            if preimageBits.[bitIdx] then 1,1 else 0,0
        else 0,1
    let state = Array.init (32*81) (init_state_from_bounds initialSetBounds)
    member __.Domain r i = (__ :> IDomainStore).Domain r i
    member __.InitialSetBounds r i = (__ :> IDomainStore).InitialSetBounds r i
    member __.ChangeBounds r i s = (__ :> IDomainStore).ChangeBounds r i s
    member __.State = state
    interface IDomainStore with
        member __.Domain r i =
            if r > 80 then initialDomain // always the same, because I'll never want to restrict this.
            elif r = -1 then Set.singleton (if 0xf9b5713du.[i] then 1 else 0)
            elif r = -2 then Set.singleton (if 0x5d6e7f4cu.[i] then 1 else 0)
            elif r = -3 then Set.singleton (if 0x192a3b08u.[i] then 1 else 0)
            elif r = -4 then Set.singleton (if 0xe970f861u.[i] then 1 else 0)
            else state.[r*32+i]
        member __.InitialSetBounds r i = initialSetBounds r i
        member __.ChangeBounds r i s = state.[r*32+i] <- s

type WDomainStore(dwlen) as __ =
    let initialSetBounds r i =
        let n = 32*r+i
        if n < int dwlen || n > 511 then 0,1
        else (if constantValue dwlen n then 1,1 else 0,0)
    let state = Array.init (32*80) (init_state_from_bounds initialSetBounds)
    member __.DWLen = dwlen
    member __.Domain r i = (__ :> IDomainStore).Domain r i
    member __.InitialSetBounds r i = (__ :> IDomainStore).InitialSetBounds r i
    member __.ChangeBounds r i s = (__ :> IDomainStore).ChangeBounds r i s
    member __.State = state
    interface IDomainStore with
        member __.Domain r i =
            state.[r*32+i]
        member __.InitialSetBounds r i = initialSetBounds r i
        member __.ChangeBounds r i s = state.[r*32+i] <- s

type VDomainStore() as __ =
    let initialSetBounds _ i = 0,7 // screw it.  Seems to make other logic easier, for now.
        //match i with | 26 -> 0,5 | 25 -> 0,6 | _ -> 0,7
    // the state (r,i) here tracks the carry FROM a particular column.
    let state = Array.init (32*81) (init_state_from_bounds initialSetBounds)
    let v0HasCarrySet = Set.ofArray [|2;3;6;7|]
    let v0NoCarrySet = Set.ofArray [|0;1;4;5|]
    let v1HasCarrySet = Set.ofArray [|4;5;6;7|]
    let v1NoCarrySet = Set.ofArray [|0;1;2;3|]

    member __.SeparateCarries r i = // this is the (r,i) of the target.
        // because (r,i) is the carry of the target, I want to look at i+1 for the v0 and i+2 for the v1.
        let v0, v1 =
            if i=26 then Set.singleton 0, Set.singleton 0
            elif i=25 then __.Domain r 26, Set.singleton 0
            else __.Domain r ((i+1)%32), __.Domain r ((i+2)%32)
        let d0 = Set.difference v0 v0HasCarrySet // if d0 is empty, then v0 contained only members of the v0HasCarrySet
        let d0' = Set.difference v0 v0NoCarrySet // if d0' is empty, then v0 contained only members of the v0NoCarrySet
        let carry0 =
            match Set.isEmpty d0, Set.isEmpty d0' with
            | false, false -> None // I can't say anything here.  It's a mix of values. 
            | true, false -> Some true // it contains only members of v0HasCarrySet
            | false, true -> Some false // it contains only members of v0NoCarrySet
            | true, true -> failwithf "Set logic has failed.  What the bleep, in carry0? v0=%A, d0=%A, d0'=%A" v0 d0 d0'
        let d1 = Set.difference v1 v1HasCarrySet // if d1 is empty, then v1 contained only members of the v1HasCarrySet
        let d1' = Set.difference v1 v1NoCarrySet // if d1' is empty, then v1 contained only members of the v1NoCarrySet
        let carry1 =
            match Set.isEmpty d1, Set.isEmpty d1' with
            | false, false -> None // I can't say anything here.  It's a mix of values. 
            | true, false -> Some true // it contains only members of v1HasCarrySet
            | false, true -> Some false // it contains only members of v1NoCarrySet
            | true, true -> failwithf "Set logic has failed.  What the bleep, in carry1? v1=%A, d1=%A, d1'=%A" v1 d1 d1'
        carry0, carry1

    member __.CarryIndicated r i = // this is the (r,i) of the target.
        let carry0, carry1 = __.SeparateCarries r i
        match carry0, carry1 with
        | None, _ | _, None -> None // I can't say anything definitive about this.  (check later: Can I??)
        | Some false, Some false | Some true, Some true -> Some false // NO carry is indicated.
        | Some true, Some false | Some false, Some true -> Some true // YES, a 1-bit overall carry is indicated.

    member __.Domain r i = (__ :> IDomainStore).Domain r i
    member __.InitialSetBounds r i = (__ :> IDomainStore).InitialSetBounds r i
    member __.ChangeBounds r i s = (__ :> IDomainStore).ChangeBounds r i s
    member __.State = state

    interface IDomainStore with
        member __.Domain r i =
            state.[r*32+i]
        member __.InitialSetBounds r i = initialSetBounds r i // this is the (r,i) of the target
        member __.ChangeBounds r i s = state.[r*32+i] <- s

// this "steps down" (or "up"?), propagating as necessary, and spewing copious amounts of verbiage.
type Stepper(adb : ADomainStore, wdb : WDomainStore, vdb : VDomainStore) =
    let w_eqn r i =
        let constants, variables = Words.can_affect r i |> Array.partition (fun i -> i >= int wdb.DWLen)
        // the 'constants' will end up telling us whether or not to invert the 'result'.
        // let's say that our equation is a + b + c = (1|0)
        // Now, on the LHS, there's also a constant-1 result.  So it's actually
        // a + b + c + 1 = (1|0)
        // Which works out to being the same as
        // a + b + c = ~(1|0)
        // Because we can subtract that 1 from both sides.
        let constResult =
            match constants |> Array.map (Words.constantValue wdb.DWLen) with
            | [||] | [|false|] -> false
            | [|true|] -> true
            | xs -> (Seq.filter ((=) true) xs |> Seq.length) % 2 = 1
        variables, constResult

    let reevaluateV r i = // this is the (r,i) of the column that I'm adding up to get that "V".
        let mutable lower, upper = vdb.InitialSetBounds r i
        // If a particular value is fixed =1, then we increase the set lower-bound by 1.
        // If a particular value is fixed =0, then we decrease the set upper-bound by 1.
        let t = { Round=r; Bit=i; Var=V.A }
        let a,f,e,w,_,_ = Keys.inputKeys_overall t
        if Utilities.kbit t then lower <- lower + 1
        else upper <- upper - 1
        let modBounds x (db : IDomainStore) =
            let v = db.Domain x.Round x.Bit
            if v = Set.singleton 1 then lower <- lower + 1
            elif v = Set.singleton 0 then upper <- upper - 1
        modBounds a adb
        do // want to keep /v/ out of scope
            let v = f_domain f adb
            if v = Set.singleton 1 then lower <- lower + 1
            elif v = Set.singleton 0 then upper <- upper - 1
        modBounds e adb
        modBounds w wdb
        match vdb.SeparateCarries r i with
        | None, None -> ()
        | Some true, Some false | Some false, Some true ->
            upper <- upper - 1
            lower <- lower + 1
        | Some true, Some true -> lower <- lower + 2
        | Some false, Some false -> upper <- upper - 2
        | None, Some true | Some true, None -> lower <- lower + 1
        | None, Some false | Some false, None -> upper <- upper - 1
        let newBounds = Set.ofSeq {lower..upper}
        if vdb.Domain r i <> newBounds then
            printfn "V-evaluation for column a(%d,%d): New bounds: [%d,%d]" r i lower upper
            vdb.ChangeBounds r i newBounds
            vdb.CarryIndicated r i
            |> Option.iter (fun carry ->
                printfn "There %s a carry for target a(%d,%d)" (if carry then "was" else "wasn't") r i
                //addConstraintType0(r, i, if carry then 1 else 0)
            )
            true
        else false

    let reevaluateW r i = // the (r,i) is the target 'a'
        let _,_,_,w,_,_ = Keys.inputKeys_overall {Round=r; Bit=i; Var=V.A}
        let mutable eqn, constant = w_eqn w.Round w.Bit
        // take a look at the domains of each of the eqn things.  If it's constant,
        // then put it on the constant side.
        eqn <- eqn |> Array.filter (fun vIdx ->
            let v = wdb.Domain (vIdx/32) (vIdx%32)
            if Set.count v = 1 then
                if v = Set.singleton 1 then constant <- not constant // flip it.
                false // remove it from eqn
            else true // keep it in eqn.
        )
        // check if it works out to a constant.
        match eqn with
        | [||] -> // then it's equivalent to the constant.
            let newBound = Set.singleton (if constant then 1 else 0)
            if wdb.Domain w.Round w.Bit <> newBound then
                //printfn "W-evaluation for a(%d,%d): New value: %A" r i newBound
                wdb.ChangeBounds w.Round w.Bit newBound
                true
            else false
        | _ ->
            // do nothing.
            //addConstraintType1(r, i, eqn, constant)
            false

    let reevaluateA r i = // the (r,i) is the target "a"
        // if I already know what it is ... skip this.
        if Set.count (adb.Domain r i) = 1 then
            false
        else
            let t = { Round=r; Bit=i; Var=V.A }
            let a,f,e,w,_,_ = Keys.inputKeys_overall t
            let f = f_domain f adb
            let a, e, w = adb.Domain a.Round a.Bit, adb.Domain e.Round e.Bit, wdb.Domain w.Round w.Bit
            let v =
                match vdb.CarryIndicated r i with
                | Some true -> Set.singleton 1 | Some false -> Set.singleton 0
                | _ -> Set.ofArray [|0;1|]
            //printfn "%A %A %A %A %A" a f e w v
            if Set.count a = 1 && Set.count f = 1 && Set.count e = 1 && Set.count w = 1 && Set.count v = 1 then
                // I can definitively work out what this is.
                let a, f, e, w, v = Seq.head a, Seq.head f, Seq.head e, Seq.head w, Seq.head v
                let k = if Utilities.kbit t then 1 else 0
                if (a+f+e+w+v+k)%2=1 then adb.ChangeBounds r i (Set.singleton 1)
                else adb.ChangeBounds r i (Set.singleton 0)
                printfn "A-evaluation for a(%d,%d): New value: %A" r i (adb.Domain r i)
                // put in a constraint here?
                //addConstraintType2(r, i, val)
                true
            else false

    member __.Apply () =
        for (r,i) in Utilities.bitProgression (1,26) 81 do
            // let's look at the constraints.
            // The first one that I'll look at is "V".
            if reevaluateV r i then ()
            // then I'll look at "W".
            if reevaluateW r i then ()
            // lastly, I'll look at "A".
            if reevaluateA r i then ()

//let dwlen = 0u
//let hashString = "72f480ed6e9d9f84999ae2f1852dc41aec052519"
let dwlen = 2u
let hashString = "71c10ea23fe185e1eefe7b2dea1bb12cb35d23da" // related input data for this 2-bit hash is: ff
//let dwlen = 6u
//let hashString = "261f6b322cb0ca9eabc2ea17d0211af21dd90720" // related input data for this 6-bit hash is: ac
let adb = ADomainStore(hashString)
let wdb = WDomainStore(dwlen)
let vdb = VDomainStore()
let stepper = Stepper(adb, wdb, vdb)

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
// a dictionary to do Designator --> BDD lookups
let designator_to_var_map = System.Collections.Generic.Dictionary<_,_>()
// put in the constants.
SubCalculations.Internal.init_subcalc_constants dwlen storage repr
// the call to make_preimage_bdd will give back a BDD, AND a designator-to-variable-map.
// No variables for r=80..76 exist, because they have been replaced by constants.
// The designator-to-variable map here refers to variables from r=75.
let mutable preimage_bdd = make_preimage_bdd wb designator_to_var_map bdd_o hashBits storage dwlen


let arr = Array.init 78 (fun i -> make_a_bdds dwlen wb designator_to_var_map bdd_o storage (79-i))
