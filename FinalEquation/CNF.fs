namespace FinalEquation.CNF

type Term =
| Var of int
| True
| False

type Clause =
| OneCNF of Term
| TwoCNF of Term * Term
| ThreeCNF of Term * Term * Term

type CNF = Clause []

module Common =
    let dimacsFormat clauses =
        use ms = new System.IO.MemoryStream()
        using (new System.IO.StreamWriter(ms, System.Text.Encoding.ASCII, 4096, true)) (fun tw ->
            let numVars =
                1 + (clauses
                |> Seq.collect (fun x ->
                    match x with
                    | OneCNF (Var x) -> [|abs x|]
                    | TwoCNF (Var a, Var b) -> [|abs a; abs b|]
                    | ThreeCNF (Var a, Var b, Var c) -> [|abs a; abs b; abs c|]
                    | _ -> Array.empty
                ) |> Seq.distinct
                |> Seq.length)
            let numClauses = Seq.length clauses
            tw.WriteLine ("p cnf {0} {1}", numVars, numClauses)
            clauses
            |> Seq.iter (function
                | TwoCNF (Var a, Var t) -> tw.WriteLine ("{0} {1} 0", a, t)
                | ThreeCNF (Var a, Var b, Var t) -> tw.WriteLine("{0} {1} {2} 0", a, b, t)
                | OneCNF (Var x) -> tw.WriteLine("{0} 0", x)
                | x -> failwithf "Unexpected item to write: %A" x
            )
        )
        ms.Seek(0L, System.IO.SeekOrigin.Begin) |> ignore
        use s = new System.IO.StreamReader(ms)
        s.ReadToEnd()
    
    open FinalEquation.CommonStructure

    let evaluatedFor (dwlen : uint32) clauses conv (data : uint32[]) =
        let d = System.Collections.Generic.Dictionary()
        for i = 0 to int dwlen - 1 do
            d.[i+1] <- data.[i/32].[i%32]
        for clause in clauses do
            match clause with
            | ThreeCNF (Var a,Var b,Var t) ->
                if not <| d.ContainsKey (abs t) then
                    let aVal = if a>0 then d.[a] else not d.[-a]
                    let bVal = if b>0 then d.[b] else not d.[-b]
                    if aVal = false && bVal = false then
                        d.[abs t] <- t > 0 // must be, to make the clause true.
            | TwoCNF (Var x,Var t) ->
                if not <| d.ContainsKey (abs t) then
                    if d.ContainsKey x = false && d.ContainsKey -x = false then
                        System.Diagnostics.Debugger.Break ()
                    let xVal = if x>0 then d.[x] else not d.[-x]
                    if xVal = false then
                        d.[abs t] <- t > 0 // must be, to make this clause true.
            | OneCNF (Var t) ->
                // this must be true!
                if not <| d.ContainsKey (abs t) then
                    d.[abs t] <- t > 0 // must be, to make this clause true
            | x -> failwithf "Unexpected clause: %A" x
        fun point ->
            match conv point with
            | False -> false
            | True -> true
            | Var v ->
                assert(if v > 0 then d.ContainsKey v else d.ContainsKey -v)
                if v > 0 then d.[v] else not d.[-v]
