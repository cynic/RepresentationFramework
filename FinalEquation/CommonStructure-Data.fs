namespace FinalEquation.CommonStructure

type V = 
    | A = 0uy
    | F = 1uy
    | W = 2uy
    | V0 = 3uy
    | V1 = 4uy

//[<Struct; StructuralEquality; StructuralComparison>]
type Designator = {
    //val DWLen : uint32
    Round : int // 0..79
    Bit : int // 0..31
    Var : V
}
 (*   
    new(dwlen, round, bit, var) = 
        { DWLen = dwlen
          Round = round
          Bit = bit
          Var = var }
*)
with
    override __.ToString() = //sprintf "%d,%A,%d,%d" __.DWLen __.Var __.Round __.Bit
        System.String.Format("{0},{1},{2}", __.Var, __.Round, __.Bit)
    /// No, not mathematical π.  This is a tuple of (Position, Index)
    member __.PI with get () = __.Round, __.Bit
    member __.S
        with get () =
            let n = __.Round*32 + __.Bit
            match __.Var with
            | V.A -> sprintf "a%04d" n
            | V.F -> sprintf "f%04d" n
            | V.W -> sprintf "w%04d" n
            | V.V0 -> sprintf "v0.%04d" n
            | V.V1 -> sprintf "v1.%04d" n
            | _ -> failwithf "Unknown var %A" __.Var

type Msg = 
    | And of Designator * Designator
    | Or of Designator * Designator
    | Not of Designator

[<AutoOpen>]
module Extensions =
    type System.UInt32 with
        member inline __.Item i = (0x80000000u >>> i) &&& __ <> 0u
        member __.Bits = Seq.init 32 (fun i -> __.[i])
        member __.IndexedBits = Seq.init 32 (fun i -> i, __.[i])
        member __.BitsFromRight = Seq.init 32 (fun i -> __.[31 - i])

type Constants<'T> = {
    Zero : 'T
    One : 'T
}

module Keys =
    /// Returns a,b,c,d,e,v0,v1 rev-deps for a /t/ target a-designator
    let revDeps_overall (t : Designator) =
        if t.Var <> V.A then failwith "revDeps_overall can only be used with a-values"
        let offset2 = (t.Bit+2) % 32
        let offset27 = (t.Bit+27) % 32
        let offset31 = (t.Bit+31) % 32
        let offset30 = (t.Bit+30) % 32
        let rev_e = if t.Round > 75 then None else Some ({ Round=t.Round+5; Bit=offset2; Var=V.A })
        let rev_d = if t.Round > 76 then None else Some ({ Round=t.Round+4; Bit=offset2; Var=V.A })
        let rev_c = if t.Round > 77 then None else Some ({ Round=t.Round+3; Bit=offset2; Var=V.A })
        let rev_b = if t.Round > 78 then None else Some ({ Round=t.Round+2; Bit=t.Bit; Var=V.A })
        let rev_a = if t.Round > 79 then None else Some ({ Round=t.Round+1; Bit=offset27; Var=V.A })
        let rev_v0 = if t.Bit = 27 then None else Some ({ Round=t.Round; Bit=offset31; Var=V.A })
        let rev_v1 = if t.Bit = 27 || t.Bit = 28 then None else Some ({ Round=t.Round; Bit=offset30; Var=V.A })
        rev_a, rev_b, rev_c, rev_d, rev_e, rev_v0, rev_v1

    /// Returns a,f,e,w,v0,v1
    let inputKeys_overall (t : Designator) = 
        let offset5 = (t.Bit + 5) % 32
        let offset30 = (t.Bit + 30) % 32
        let a = { Round=t.Round - 1; Bit=offset5; Var=V.A }
        let f = { Round=t.Round - 1; Bit=offset5; Var=V.F }
        let e = { Round=t.Round - 5; Bit=offset30; Var=V.A }
        let w = { Round=t.Round - 1; Bit=offset5; Var=V.W }
        let v0 = if t.Bit = 26 then None else Some ({ Round=t.Round; Bit=t.Bit; Var=V.V0 })
        let v1 = if t.Bit = 26 || t.Bit = 25 then None else Some ({ Round=t.Round; Bit=t.Bit; Var=V.V1 })
        a, f, e, w, v0, v1
    
    /// Returns b,c,d
    let inputKeys_f (t : Designator) = 
        let offset25 = (t.Bit + 25) % 32
        let offset27 = (t.Bit + 27) % 32
        let b = { Round=t.Round - 1; Bit=offset27; Var=V.A }
        let c = { Round=t.Round - 2; Bit=offset25; Var=V.A }
        let d = { Round=t.Round - 3; Bit=offset25; Var=V.A }
        b, c, d
    
    /// Returns a,f,e,w,v0,v1
    let inputKeys_v0 (t : Designator) = 
        let offset6 = (t.Bit + 6) % 32
        let offset1 = (t.Bit + 1) % 32
        let offset31 = (t.Bit + 31) % 32
        let a = { Round=t.Round - 1; Bit=offset6; Var=V.A }
        let f = { Round=t.Round - 1; Bit=offset6; Var=V.F }
        let e = { Round=t.Round - 5; Bit=offset31; Var=V.A }
        let w = { Round=t.Round - 1; Bit=offset6; Var=V.W }
        let v0 = if t.Bit = 26 then None else Some ({ Round=t.Round; Bit=offset1; Var=V.V0 })
        let v1 = if t.Bit = 26 || t.Bit = 25 then None else Some ({ Round=t.Round; Bit=offset1; Var=V.V1 })
        a, f, e, w, v0, v1
    
    /// Returns a,f,e,w,v0,v1
    let inputKeys_v1 (t : Designator) = 
        let offset7 = (t.Bit + 7) % 32
        let offset2 = (t.Bit + 2) % 32
        let a = { Round=t.Round - 1; Bit=offset7; Var=V.A }
        let f = { Round=t.Round - 1; Bit=offset7; Var=V.F }
        let e = { Round=t.Round - 5; Bit=t.Bit; Var=V.A }
        let w = { Round=t.Round - 1; Bit=offset7; Var=V.W }
        let v0 = if t.Bit = 26 then None else Some ({ Round=t.Round; Bit=offset2; Var=V.V0 })
        let v1 = if t.Bit = 26 || t.Bit = 25 then None else Some ({ Round=t.Round; Bit=offset2; Var=V.V1 })
        a, f, e, w, v0, v1

type SubCalcRecursionResponse<'T> =
/// Yes, recurse down and fulfil this constraint.
| Yes
/// Instead of recursing down, use this value, if an existing one doesn't do the trick.
| InsteadUse of (unit -> 'T)

type SubCalcRecursion<'T> =
| Always
| Never
| Depends of (Designator -> SubCalcRecursionResponse<'T>)

module Constants = 
    [<Literal>]
    let H0 = 0x67452301u
    [<Literal>]
    let H1 = 0xEFCDAB89u
    [<Literal>]
    let H2 = 0x98BADCFEu
    [<Literal>]
    let H3 = 0x10325476u
    [<Literal>]
    let H4 = 0xC3D2E1F0u

type ICalculator<'T> =
    abstract Not : 'T -> 'T
    abstract And : 'T -> 'T -> 'T
    abstract Or : 'T -> 'T -> 'T
    abstract Xor : 'T -> 'T -> 'T
    abstract Constants : Constants<'T>
    abstract IsOne : 'T -> bool
    abstract IsZero : 'T -> bool
    abstract MakeVariable : uint32 -> 'T

type IEvaluable<'T> =
    abstract Evaluate : uint32 [] -> 'T -> bool
    abstract EvaluationCache : uint32[] -> ('T -> bool) option

type IRepresentation<'T> =
    inherit System.IDisposable
    inherit ICalculator<'T>
    inherit IEvaluable<'T>

type ISnapshot<'T,'U> =
    abstract Checkpoint : 'T * ?what:Designator -> 'U
    abstract Retrieve : 'U -> 'T

type IStorage<'T> =
    abstract Get : Designator -> 'T
    abstract GetOrGenerate : Designator -> (Designator -> 'T) -> 'T
    abstract Item : Designator -> 'T
    abstract Store : Designator -> 'T -> unit
    abstract StoreINE : Designator -> 'T -> unit
    abstract Delete : Designator -> unit
    abstract DeleteAllExcept : (Designator -> bool) -> unit
    abstract Clear : unit -> unit
    abstract Exists : Designator -> bool
    abstract ToSecondaryStorage : unit -> unit
    abstract FromSecondaryStorage : unit -> unit

type IWords<'T> =
    abstract Word : Designator -> 'T
    abstract Word : int * int -> 'T

type ISubCalculator<'T> =
    abstract A : Designator -> 'T
    abstract F : Designator -> 'T
    abstract W : Designator -> 'T
    abstract V0 : Designator -> 'T
    abstract V1 : Designator -> 'T
    abstract Item : Designator -> 'T
