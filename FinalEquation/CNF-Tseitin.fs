namespace FinalEquation.CNF.Tseitin

open FinalEquation.CommonStructure
open FinalEquation.CNF

type ConjunctiveNormalForm(dwlen : uint32) = 
    let clauses = System.Collections.Generic.List()

    let nextTseitin =
        let mutable v = int dwlen + 1
        fun () ->
            v <- v + 1
            v

    let _not (clauses : System.Collections.Generic.List<_>) x =
        match x with
        | True -> False
        | False -> True
        | Var x ->
            let tseitin = nextTseitin ()
            clauses.Add <| TwoCNF (Var -x, Var -tseitin)
            clauses.Add <| TwoCNF (Var x, Var tseitin)
            Var tseitin

    let _and (clauses : System.Collections.Generic.List<_>) a b =
        match a, b with
        | True, x | x, True -> x // no change
        | False, x | x, False -> False
        | Var a, Var b ->
            let tseitin = nextTseitin ()
            clauses.Add <| ThreeCNF (Var -a, Var -b, Var tseitin)
            clauses.Add <| TwoCNF (Var a, Var -tseitin)
            clauses.Add <| TwoCNF (Var b, Var -tseitin)
            Var tseitin

    let _or (clauses : System.Collections.Generic.List<_>) a b =
        match a, b with
        | False, x | x, False -> x // no change
        | True, x | x, True -> True
        | Var a, Var b ->
            let tseitin = nextTseitin ()
            clauses.Add <| ThreeCNF (Var a, Var b, Var -tseitin)
            clauses.Add <| TwoCNF (Var -a, Var tseitin)
            clauses.Add <| TwoCNF (Var -b, Var tseitin)
            Var tseitin

    let _xor (clauses : System.Collections.Generic.List<_>) a b =
        match a, b with
        | True, x | x, True -> // then negate.
            _not clauses x
        | False, x | x, False -> x // no change.
        | Var a, Var b ->
            let tseitin = nextTseitin ()
            clauses.Add <| ThreeCNF (Var -a, Var -b, Var -tseitin)
            clauses.Add <| ThreeCNF (Var -a, Var b, Var tseitin)
            clauses.Add <| ThreeCNF (Var a, Var -b, Var tseitin)
            clauses.Add <| ThreeCNF (Var a, Var b, Var -tseitin)
            Var tseitin
    
    let evaluatedFor (data : uint32[]) =
        Common.evaluatedFor dwlen clauses id data
    
    let evaluate (data : uint32[]) = fun point -> evaluatedFor data point

    member __.asDIMACS expected_true =
        let c' = new System.Collections.Generic.List<_>(clauses)
        c'.Add(OneCNF expected_true)
        Common.dimacsFormat c'
        
    interface IRepresentation<Term> with
        
        member __.Constants = 
            { Zero = False
              One = True }
        
        member __.And a b = _and clauses a b
        member __.Or a b = _or clauses a b
        member __.Xor a b = _xor clauses a b
        
        member __.Not x =  _not clauses x
        
        member __.MakeVariable i = Var (int i+1)
        member __.Evaluate data point = evaluate data point
        member __.EvaluationCache data = Some (evaluatedFor data)
        member __.IsZero x = x = False
        member __.IsOne x = x = True
        member __.Dispose () = ()