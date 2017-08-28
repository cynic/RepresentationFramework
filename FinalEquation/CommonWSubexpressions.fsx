#load "Words.fs"
open FinalEquation.Words

// this is for the "Common subexpressions" part of the message-expansion discussion.

let dictToArray (d : #System.Collections.Generic.IDictionary<_,_>) =
    d |> Seq.map (fun kvp -> kvp.Value, kvp.Key)
    |> Seq.groupBy fst
    |> Seq.map (fun (k,v) -> k, Seq.map snd v |> Seq.toArray)
    |> Seq.sortDescending
    |> Seq.toArray

/// which pairs appear most frequently in combination?
let pairs () =
    let pairStructure = System.Collections.Generic.Dictionary<_,_>()
    let incr (r0, i0) (r1, i1) =
        // need to track:
        // - the BASE round.
        // - the DIFFERENCE betwen rounds.
        // - the DIFFERENCE between bits.
        let baseR, dR, dI = r1, r0-r1, i0-i1
        let key = baseR, (dR, dI)
        if not <| pairStructure.ContainsKey key then
            pairStructure.[key] <- 1
        else pairStructure.[key] <- pairStructure.[key] + 1
    for round = 0 to 79 do
        let basis = constraintForms.[round]
        for i = 0 to basis.Length-1 do
            for j = i+1 to basis.Length-1 do
                incr basis.[i] basis.[j]
    dictToArray pairStructure

(*
let triples () =
    let tripleStructure =
        Array.init 512 (fun _ -> Array.init 512 (fun _ -> Array.zeroCreate 512))
    let inline incr p0 p1 p2 =
        let v = tripleStructure.[p0].[p1].[p2] + 1uy
        tripleStructure.[p0].[p1].[p2] <- v
        tripleStructure.[p1].[p2].[p0] <- v
        tripleStructure.[p2].[p0].[p1] <- v
        tripleStructure.[p0].[p2].[p1] <- v
        tripleStructure.[p1].[p0].[p2] <- v
        tripleStructure.[p2].[p1].[p0] <- v
    for round = 0 to 79 do
        for bit = 0 to 31 do
            let basis = can_affect round bit
            for i = 0 to basis.Length-1 do
                for j = i+1 to basis.Length-1 do
                    for k = j+1 to basis.Length-1 do
                        incr basis.[i] basis.[j] basis.[k]
    tripleStructure
*)

/// which triples appear most frequently in combination?
let triples () =
    let triplesStructure = System.Collections.Concurrent.ConcurrentDictionary()
    let incr (r0, i0) (r1, i1) (r2, i2) =
        let baseR, dR0, dI0, dR1, dI1 = r2, r1-r2, i1-i2, r0-r2, r0-i2
        let key = baseR, (dR0, dI0), (dR1, dI1)
        triplesStructure.AddOrUpdate(key, 1, fun _ v -> v+1) |> ignore
    for round = 0 to 79 do
        let basis = constraintForms.[round]
        [|0..basis.Length-1|] |> Array.Parallel.iter (fun i ->
            [|i+1..basis.Length-1|] |> Array.Parallel.iter (fun j ->
                for k = j+1 to basis.Length-1 do
                    incr basis.[i] basis.[j] basis.[k]
            )
        )
    dictToArray triplesStructure

// takes about 8.5 minutes to complete
let quads () =
    let quadsStructure = System.Collections.Concurrent.ConcurrentDictionary()
    let incr (r0, i0) (r1, i1) (r2, i2) (r3, i3) =
        let key = r3, (r2-r3, i2-i3), (r1-r3, i1-i3), (r0-r3, i0-i3)
        quadsStructure.AddOrUpdate(key, 1, fun _ v -> v+1) |> ignore
    for round = 0 to 79 do
        let basis = constraintForms.[round]
        [|0..basis.Length-1|] |> Array.Parallel.iter (fun i ->
            [|i+1..basis.Length-1|] |> Array.Parallel.iter (fun j ->
                [|j+1..basis.Length-1|] |> Array.Parallel.iter (fun k ->
                    for l = k+1 to basis.Length-1 do
                        incr basis.[i] basis.[j] basis.[k] basis.[l]
                )
            )
        )
    dictToArray quadsStructure

(*
// takes roughly 7 minutes to run.
let frequentTriples (trips : _[][][]) =
    let d = System.Collections.Generic.List()
    for i = 0 to trips.Length-1 do
        for j = i+1 to trips.[i].Length-1 do
            for k = j+1 to trips.[i].[j].Length-1 do
                //if trips.[i].[j].[k] > 0uy then
                    d.Add( trips.[i].[j].[k], (i,j,k) )
    d.Sort()
    d.Reverse()
    d.ToArray ()
*)

let neverTogether () =
    let neverStructure =
        System.Collections.Generic.SortedSet(
            seq {
                for r = 0 to 15 do
                    for b = 0 to 31 do
                        for r' = 0 to 15 do
                            for b' = 0 to 31 do
                                yield (r,b),(r',b')
            }
        )
    let inline kill (r0,i0) (r1,i1) =
        for i = 0 to 31 do
            let a = r0,(i0+i)%32
            let b = r1,(i1+i)%32
            let v = a,b
            let v' = b,a
            neverStructure.Remove v |> ignore
            neverStructure.Remove v' |> ignore
    // find the things that never intersect (inefficiently)
    for round = 0 to 79 do
        let basis = constraintForms.[round]
        for i = 0 to basis.Length-1 do
            for j = i+1 to basis.Length-1 do
                kill basis.[i] basis.[j]
    neverStructure |> Seq.toArray

let nT = neverTogether ()
let nT' = nT |> Seq.groupBy fst |> Seq.map (fun (k,vx) -> k, vx |> Seq.map snd |> Seq.toArray) |> Seq.toArray
let nT'c = nT' |> Array.map (fun (k,vx) -> k, Array.length vx)
let nT'' = nT' |> Array.filter (fun ((_,v),_) -> v=0) |> Array.map (fun ((r,_),v) -> r,v)
let nT''c = nT'' |> Array.map (fun (k,vx) -> k, Array.length vx)

#r "bin/Debug/FsPickler.dll"
open Nessos.FsPickler
open System.IO

let pickler = FsPickler.CreateBinarySerializer()
let p = pairs ()
let t = triples ()
let q = quads ()
using (File.Create(@"C:\Temp\w_pairs.dat")) (fun f ->
    let arr = pickler.Pickle(p) // num_calcs * (baseRound * (rOffset * iOffset))
    f.Write(arr, 0, arr.Length)
)
using (File.Create(@"C:\Temp\w_triples.dat")) (fun f ->
    let arr = pickler.Pickle(t) // num_calcs * (baseRound * (rOffset * iOffset) * (rOffset * iOffset))
    f.Write(arr, 0, arr.Length)
)
using (File.Create(@"C:\Temp\w_quads.dat")) (fun f ->
    let arr = pickler.Pickle(q) // num_calcs * (baseRound * (rOffset * iOffset) * (rOffset * iOffset) * (rOffset * iOffset))
    f.Write(arr, 0, arr.Length)
)


// to print out to LaTeX
module LaTeX =
    let pm x = if x >= 0 then sprintf "+%d" x else sprintf "%d" x
    let pairString (r,(a,b)) = sprintf "$%d|_{%s}^{%s}$" r (pm a) (pm b)
    let tripleString (r,(a,b),(c,d)) = sprintf "$%d|_{%s}^{%s}|_{%s}^{%s}$" r (pm a) (pm b) (pm c) (pm d)
    let quadString (r,(a,b),(c,d),(e,f)) = sprintf "$%d|_{%s}^{%s}|_{%s}^{%s}|_{%s}^{%s}$" r (pm a) (pm b) (pm c) (pm d) (pm e) (pm f)
    let stringed out xs =
        xs |> Array.map out
        |> String.concat ", "
    let printOut out xs =
        xs
        |> Seq.iter (fun (k,vx) -> printfn "%d & %s \\\\" k (stringed out vx))
