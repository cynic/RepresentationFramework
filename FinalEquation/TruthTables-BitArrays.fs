namespace FinalEquation.TruthTables.BitArrays
open FinalEquation.CommonStructure
open System.Collections

module Options =
    [<Literal>]
    let RecordCompressionRatios = false
    [<Literal>]
    let UseCompression = false

open Options

type TTable = BitArray

module Internal =
    let size dwlen = // in bits
        let actual = 2.**(float dwlen) |> int
        if actual % 8 = 0 then actual
        else (actual/8+1)*8 // inefficient padding :)
    let private d0 = System.Collections.Concurrent.ConcurrentDictionary<int, BitArray>()
    let private d1 = System.Collections.Concurrent.ConcurrentDictionary<int, BitArray>()
    
    let one sz = d1.GetOrAdd(sz, fun n -> BitArray(sz, true))
    let zero sz = d0.GetOrAdd(sz, fun n -> BitArray(sz, false))

    let reverse x =
        // via http://graphics.stanford.edu/~seander/bithacks.html#BitReverseObvious
        let inline reverseByte b =
            ((uint64 b * 0x80200802UL) &&& 0x0884422110UL) * 0x0101010101UL >>> 32 |> byte |> uint32
        let a = byte (x >>> 24) |> reverseByte
        let b = byte ((x &&& 0x00ff0000u) >>> 16) |> reverseByte
        let c = byte ((x &&& 0x0000ff00u) >>> 8) |> reverseByte
        let d =  byte (x &&& 0xffu) |> reverseByte
        // now put them together as d,c,b,a
        let result = (d <<< 24) ||| (c <<< 16) ||| (b <<< 8) ||| a 
        result

open Internal

// only works for dwlen < 32.  But I don't want to go above that anyway, storage
// requirements become a bit prohibitive.
type TruthTable(dwlen : uint32) =
    let size = size dwlen
    let terminator = 0x1u <<< int dwlen

    static member IndexToInputBitvector idx = uint32 idx |> reverse
    interface IRepresentation<TTable> with
        member __.And a b = (new BitArray(a)).And b
        member __.Or a b = (new BitArray(a)).Or b
        member __.Xor a b = (new BitArray(a)).Xor b
        member __.Not x = (new BitArray(x)).Not()
        member __.MakeVariable n =
            let r = new BitArray(size, false)
            let blitSize = 2.**float n |> int
            let jumpSize = blitSize
            let iterCount = size / (jumpSize+blitSize)
            let rec onSet count pos =
                if count < iterCount then
                    for j = 0 to blitSize-1 do
                        r.[pos+j] <- true
                    onSet (count+1) (pos+jumpSize+blitSize)
            onSet 0 jumpSize
            r
        member __.Evaluate data point =
            let reversed = reverse data.[0]
            let idx = int (reversed ^^^ terminator) // mask out the terminator
            point.[idx]
        member __.EvaluationCache data =
            let reversed = reverse data.[0]
            let idx = int (reversed ^^^ terminator) // mask out the terminator
            //assert (idx >= 0)
            //assert (idx < int dwlen)
            Some (fun point -> point.[idx])
        member __.Constants with get () = { Zero=zero size; One=one size }
        member __.IsZero x = x |> Seq.cast |> Seq.forall ((=) false)
        member __.IsOne x = x |> Seq.cast |> Seq.forall ((=) true)
        member __.Dispose () = ()

    interface ISnapshot<TTable,byte[]> with
        member __.Checkpoint (x, what) =
            let arr : byte[] = Array.zeroCreate (size/8)
            x.CopyTo(arr, 0)
            if UseCompression then
                let result =
                    using (new System.IO.MemoryStream(float size * 1.015 |> int)) (fun dest ->
                        using (new System.IO.MemoryStream(arr)) (fun src ->
                            using (new System.IO.Compression.DeflateStream(dest, System.IO.Compression.CompressionLevel.Optimal)) (fun cs ->
                                src.CopyTo(cs)
                            )
                        )
                        dest.ToArray ()
                    )
                if RecordCompressionRatios then
                    (*************** Tracking ratios ****************)
(*
                    what |> Option.iter (fun key ->
                        if key.Bit >= 0 && key.Round >= 0 && key.DWLen > 0u then
                            using (System.IO.File.AppendText(@"c:\temp\compressibility.csv")) (fun fs ->
                                let ratio = float result.Length / float arr.Length
                                fprintfn fs "%d,%A,%d,%f" key.DWLen key.Var (key.Bit + key.Round*32) ratio
                            )
                    )
*)
                    ()
                    (*************** /Tracking ratios ****************)
                result
            else arr
        member __.Retrieve x =
            if UseCompression then
                use dest = new System.IO.MemoryStream(size)
                using (new System.IO.MemoryStream(x)) (fun src ->
                    using (new System.IO.Compression.DeflateStream(src, System.IO.Compression.CompressionMode.Decompress)) (fun ds ->
                        ds.CopyTo(dest)
                    )
                )
                BitArray (dest.ToArray())
            else BitArray(x)

