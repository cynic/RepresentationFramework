module FinalEquation.MyBDD

open FinalEquation.CommonStructure

(*
I only care about representing a maximum of 8 inputs.
*)

type Tree =
| One
| Zero
| Node of var:int * high:Tree * low:Tree

open System.Collections.Generic

// not a ROBDD, but whatever, for now.
type BinaryDecisionDiagram(dwlen) =
    do
        if dwlen > 8u then failwith "Can only handle dwlen <= 8"

    let rec apply op a b =
        match a, b with
        | Zero, Zero | Zero, One | One, Zero | One, One -> op a b
        | Node (xV,xH,xL), Node (yV,yH,yL) when xV=yV ->
            let rL = apply op xL yL
            let rH = apply op xH yH
            Node(xV, rH, rL)
        | (Node(xV,xH,xL), (Node (yV,yH,yL) as b) | (Node(yV,yH,yL) as b), Node (xV,xH,xL)) when xV < yV ->
            let rL = apply op xL b
            let rH = apply op xH b
            Node(xV, rH, rL)
        | Node(v,h,l), ((One|Zero) as x) | ((One|Zero) as x), Node(v,h,l) ->
            let rL = apply op l x
            let rH = apply op h x
            Node(v, rH, rL)
        | _ -> failwithf "[apply] Did not consider case: %A, %A" a b

    let andF a b =
        match a,b with
        | One, x | x, One -> x
        | Zero, _ | _, Zero -> Zero
        | _ -> failwithf "[and] Did not consider case: %A, %A" a b

    let orF a b =
        match a,b with
        | One, _ | _, One -> One
        | Zero, x | x, Zero -> x
        | _ -> failwithf "[or] Did not consider case: %A, %A" a b

    let xorF a b =
        match a,b with
        | Zero, One | One, Zero -> One
        | One, One | Zero, Zero -> Zero
        | _ -> failwithf "[xor] Did not consider case: %A, %A" a b

    let _and a b = apply andF a b
    let _or a b = apply orF a b
    let _xor a b = apply xorF a b

    let rec _not x =
        match x with
        | One -> Zero
        | Zero -> One
        | Node(v,h,l) -> Node (v, _not h, _not l)

    member __.WriteDot filename tree =
        using (System.IO.File.CreateText filename) (fun f ->
            let ranks = System.Collections.Generic.Dictionary()
            let content =
                let rec descend parent thenPath node =
                    seq {
                        let style = if thenPath then "solid" else "dashed"
                        match node with
                        | One ->
                            yield sprintf """%s -> OneNode [style="%s"];""" parent style
                        | Zero ->
                            yield sprintf """%s -> ZeroNode [style="%s"];""" parent style
                        | Node(v,h,l) ->
                            if not <| ranks.ContainsKey v then
                                ranks.[v] <- System.Collections.Generic.List()
                            let myId = parent + (if thenPath then "T" else "E")
                            ranks.[v].Add (sprintf "\"%s\";" myId)
                            yield sprintf """%s [shape="ellipse" label="var%d"];""" myId v
                            yield sprintf """%s -> %s [style="%s"];""" parent myId style
                            yield! descend myId true h
                            yield! descend myId false l
                    }
                let ranking () =
                    seq {
                        for kvp in ranks do
                            yield sprintf "{ rank=same; %s }" (kvp.Value |> String.concat " ")
                    }
                Seq.append (descend "Root" true tree) (ranking ())
                |> String.concat "    \n"
            // now put it all together.
            fprintfn f "digraph bdd {"
            fprintfn f "    OneNode [shape=box label=\"1\"];"
            fprintfn f "    ZeroNode [shape=box label=\"0\"];"
            fprintfn f "    { rank=same; \"OneNode\"; \"ZeroNode\"; }"
            fprintfn f "    %s" content
            fprintfn f "}"
        )

    interface IRepresentation< Tree > with
        member __.Constants = {One=One; Zero=Zero}
        member __.And a b = _and a b
        member __.Or a b = _or a b
        member __.Xor a b = _xor a b
        member __.Not x = _not x
        member __.MakeVariable n = Node (int n, One, Zero)
        member __.Evaluate data point =
            let rec descend node =
                match node with
                | Node (v,h,l) ->
                    if data.[v/32].[v%32] then descend h
                    else descend l
                | One -> true
                | Zero -> false
            descend point
        member __.EvaluationCache data = None
        member __.IsZero x = x = Zero
        member __.IsOne x = x = One
        member __.Dispose () = ()