#r "bin/Debug/FsPickler.dll"
#load "Dependencies.fsx"
#load "AIG.fs"

open FinalEquation.CommonStructure
open FinalEquation.AIG

let aiger_with_inputs dwlen =
    let o = AndInverterGraph(dwlen)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(dwlen, r) :> IStorage<_>
    let h = HashCalculator<_>(dwlen, r, s, Traditional)

    h.GenerateRepresentation ()

    let abc = ABCInterface(dwlen)
    abc.WriteAiger(o.AAG, sprintf @"P:\test-%dinput.aig" dwlen)
    let mapOutput = Utilities.hashDesignator dwlen >> s.Get
    let outputs =
        Array.map mapOutput [|0..159|]
    // final 160 bits
    abc.WriteMultiOutputAiger (o.AAG.Ands, Array.map mapOutput [|0..159|], sprintf @"P:\test-%dinput-m.aig" dwlen)
    // first (?) 16 bits of 80th word
    abc.WriteMultiOutputAiger (o.AAG.Ands, Array.map mapOutput [|128..143|], sprintf @"P:\test-%dinput-m-p16.aig" dwlen)
    // first (?) 8 bits of 80th word
    abc.WriteMultiOutputAiger (o.AAG.Ands, Array.map mapOutput [|128..135|], sprintf @"P:\test-%dinput-m-p8.aig" dwlen)
    //abc.WriteMultiOutputAiger(o.AAG.Ands, o.AAG.Ou sprintf @"P:\test-%dinput.aig" dwlen)

