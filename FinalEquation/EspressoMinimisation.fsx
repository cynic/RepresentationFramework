//#r "bin/Release/FsPickler.dll"
#load "Dependencies.fsx"
#load "TruthTables-BitArrays.fs"

open FinalEquation.CommonStructure
open FinalEquation.TruthTables.BitArrays

let n = 12u
let workDir = @"P:\boom_data"
System.IO.Directory.CreateDirectory workDir |> ignore
let tt = TruthTable n
let repr = tt :> IRepresentation<_>
let storage = Storage.MemoryStorage<_>() :> IStorage<_>
let words = FinalEquation.Words.Traditional(n, repr, storage)
let subcalcs = SubCalculations.AndOrXorNot(n, words, SubCalcRecursion.Always, repr, storage)
let calc = HashCalculator(n, repr, storage, subcalcs)

// Each row of the truth table represents the result, when the row is the input vector.

storage.FromSecondaryStorage ()
// ... or ...
calc.GenerateRepresentation ()
storage.ToSecondaryStorage ()

let plaRows =
    [|
        for i = 0 to (2.**float n |> int)-1 do
            yield System.Convert.ToString(i, 2).PadLeft(int n, '0')
    |]

for round = 1 to 80 do
    for bit = 0 to 31 do
        // 1. read in a truth table.
        let ttable = storage.[{ Round=round; Bit=bit; Var=V.A }]
        // 2. write out a PLA.
        let fn = System.IO.Path.Combine(workDir, sprintf "%02d-%02d-%02d.pla" n round bit)
        using (System.IO.File.CreateText fn) (fun f ->
            f.WriteLine (".i {0}", n)
            f.WriteLine ".o 1"
            f.WriteLine ".type fr"
            plaRows |> Array.iteri (fun i x ->
                f.WriteLine("{0} {1}", x, if ttable.[i] then '0' else '1')
            )
        )
        // 3. minimise the PLA.
        // `-- this one can be done via shell-script calling espresso...
        // ../../espresso -oeqntott $FILENAME | tr '\n' ' ' | sed 's/ //g'