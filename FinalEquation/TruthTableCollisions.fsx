#load "Dependencies.fsx"
#load "TruthTables-BitArrays.fs"

open FinalEquation.CommonStructure
open FinalEquation.TruthTables.BitArrays

let n = 22u
let tt = TruthTable n
let repr = tt :> IRepresentation<_>
let storage = Storage.DiskStorage(n, repr) :> IStorage<_>
let calc = HashCalculator(n, repr, storage, Traditional)
calc.DeleteNonFinal <- false // true

// Each row of the truth table represents the result, when the row is the input vector.

// When two rows are the same, then we have a collision.
// We can treat this as an output bit-vector and set bits when we encounter a pattern.
// If we end up trying to set something that's already set, then we've got a collision.
// Let's start by looking at 16 bits at a time.

storage.FromSecondaryStorage ()
// ... or ...
calc.GenerateRepresentation ()
storage.ToSecondaryStorage ()

let findCloseMisses () = // going 'up' by 20 for initial check.
    let bv = Array.init 16777216 (fun _ -> System.Collections.Concurrent.ConcurrentBag()) (*i.e. 2 ^^ 20*)
    let size = 2.**(float n) |> int
    let data = Array.init (32*5) (fun idx -> storage.[Utilities.hashDesignator n idx])
    let result = System.Collections.Concurrent.ConcurrentBag()
    let best = ref 0
    let checks = ref 0
    let continueCheck idx0 idx1 =
        System.Threading.Interlocked.Increment checks |> ignore
        let mutable fit = 0
        for s = 0 to (32*5-1) do
            if data.[s].[idx0] = data.[s].[idx1] then fit <- fit + 1
        if fit >= !best then
            // there is a bit of a race issue here.  But at worst, we get slightly sub-par results; so, no
            // real worries.
            if fit > !best then
                System.Threading.Interlocked.Exchange(best, fit) |> ignore
            printfn "Best fit (thus far): %d : %d, %d = %x %x" fit idx0 idx1 (TruthTable.IndexToInputBitvector idx0) (TruthTable.IndexToInputBitvector idx1)
            result.Add (fit, idx0, idx1)
    let checkPartition start ``end`` =
        printfn "Going from %d to %d" start ``end``
        let fivepercent = float (``end``-start)/100.*5. |> int
        let idxForRow row =
            let mutable idx = 0
            //printfn "row=%d, max=%d" row (size-1)
            for j = 27 to 31 do
                idx <- idx ||| ((if data.[j].[row] then 1 else 0) <<< ((j+5)%32))
            for j = 0 to 18 do
                idx <- idx ||| ((if data.[j].[row] then 1 else 0) <<< (j+5))
            //printfn "row=%d, idx=%d" row idx
            idx
        async {
            for row = start to ``end`` do
                if row % fivepercent = 0 then
                    printfn "%d-%d: @%d" start ``end`` row
                //printfn "Going to find idx for row %d" row
                let idx = idxForRow row
                //printfn "Adding %d to bv.[%d], bv.Length=%d" row idx bv.Length
                bv.[idx].Add row
                for x in bv.[idx] do
                    if x <> row then
                        //printfn "Continuing check x=%d row=%d" x row
                        continueCheck x row // never executes if bv.[idx] is empty
            printfn "%d-%d: done" start ``end``
        }
    let interval = size/4
    printfn "Starting the checks..."
    [|
        checkPartition 0 interval
        checkPartition (interval+1) (interval*2)
        checkPartition (interval*2+1) (interval*3)
        checkPartition (interval*3+1) (size-1)
    |]
    |> Async.Parallel |> Async.Ignore |> Async.RunSynchronously
    //Async.RunSynchronously <| checkPartition 0 (size-1)
    printfn "Full checks done (%d bits): %d" n (!checks)
    result.ToArray ()

// for 24-bits, this took 3:06:20 of real time, but 11:23:40 of CPU time.

let misses = findCloseMisses () |> Array.sort
let ser = Nessos.FsPickler.BinarySerializer()
using (System.IO.File.Open(sprintf @"c:\temp\%d-bit misses.txt" n, System.IO.FileMode.Create)) (fun fs ->
    ser.Serialize(fs, misses)
)

let misses_deser = ser.Deserialize<(int*int*int)[]>(System.IO.File.OpenRead(sprintf @"c:\temp\%d-bit misses.txt" n))
misses_deser |> Seq.iter (fun (_,a,b) -> printfn "%x %x" (TruthTable.IndexToInputBitvector a) (TruthTable.IndexToInputBitvector b))

for n in [12..2..24] do
    let misses_deser =
        ser.Deserialize<(int*int*int)[]>(System.IO.File.OpenRead(sprintf @"c:\temp\%d-bit misses.txt" n))
    let min = misses_deser |> Array.minBy (fun (n,_,_) -> n) |> fun (x,_,_) -> x
    let max = misses_deser |> Array.maxBy (fun (n,_,_) -> n) |> fun (x,_,_) -> x
    let misses_map =
        misses_deser
        |> Array.map (fun (n,a,b) -> n, (a,b))
        |> Map.ofArray
    let (~%) = TruthTable.IndexToInputBitvector
    let a,b = misses_map.[min]
    printfn "%d bits: min %d: %08x %08x" n min %a %b 
    let a,b = misses_map.[max]
    printfn "%d bits: max %d: %08x %08x" n max %a %b
