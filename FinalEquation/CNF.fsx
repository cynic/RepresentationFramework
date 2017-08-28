#time
#load "Dependencies.fsx"
#load "CNF.fs"
#load "CNF-Tseitin.fs"

open FinalEquation.CommonStructure
open FinalEquation.CNF

let testInput =
    [|
        "deadbeef"; "cafebabe"; "abad1dea"; "b33fd00d"
        "01234567"; "89abcdef"; "0f1e2d3c"; "4b5a6978"
        "b01dface"; "deadbea7"; "5ca1ab1e"; "cab005e5"
        "0b501e7e"; "acc01ade"
    |] |> String.concat ""

let writeCNF dwlen w_method =
    let o = Tseitin.ConjunctiveNormalForm(dwlen)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(dwlen, r) :> IStorage<_>
    let h = HashCalculator<_>(dwlen, r, s, w_method)

    h.GenerateRepresentation()

    let pre = PreimageCalculator(r, testInput, s, dwlen)

    let sef = pre.SingleEquationForm ()
    //printfn "Output node is: %d, therefore idx=%d,inverted=%b" sef (sef/2u) (sef%2u=1u)
    printfn "Hash result is %s" pre.ExpectedOutput
    let s = o.asDIMACS sef
    System.IO.File.WriteAllText(sprintf @"p:\test_%s_%d.cnf" (string w_method) dwlen, s)

for n = 1 to 24 do
    let n = uint32 n
    writeCNF n Traditional // used for CNF simplification experiments
    writeCNF n BaseXor // used for CNF simplification experiments
    printfn "Done %d" n

writeCNF 447u Traditional
writeCNF 447u BaseXor
