#load "Dependencies.fsx"
#load "MyBDD.fs"

open FinalEquation.CommonStructure
open FinalEquation.MyBDD

let testInput =
    [|
        "deadbeef"; "cafebabe"; "abad1dea"; "b33fd00d"
        "01234567"; "89abcdef"; "0f1e2d3c"; "4b5a6978"
        "b01dface"; "deadbea7"; "5ca1ab1e"; "cab005e5"
        "0b501e7e"; "acc01ade"
    |] |> String.concat ""

let makeBdd dwlen =
    use o = new BinaryDecisionDiagram(dwlen)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(dwlen, r) :> IStorage<_>
    let h = HashCalculator<_>(dwlen, r, s, Traditional)

    h.GenerateRepresentation ()

    let pre = PreimageCalculator(r, testInput, s, dwlen)

    let fn = sprintf @"P:\mybdd_%02d-pre.dot" dwlen

    let sef = pre.SingleEquationForm ()

    o.WriteDot fn sef

//makeBdd 6u