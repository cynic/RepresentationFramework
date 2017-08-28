#load @"..\packages\FSharp.Charting.0.90.13\FSharp.Charting.fsx"
#r @"..\packages\FSharp.Data.2.2.5\lib\net40\FSharp.Data.dll"
open FSharp.Charting
open FSharp.Data

open System.IO
(*
File.ReadAllLines(@"C:\Users\Yusuf Motara\Desktop\compressibility.tsv")
|> Array.choose (fun line ->
    let split = line.Split('\t')
    if split.Length = 5 then
        try
            let dwlen, round, var, idx, ratio = int split.[0], int split.[1], split.[2], int split.[3], float (split.[4].Replace(',','.'))
            if dwlen <= 0 then None
            else Some(sprintf "%d,%s,%d,%.15f" dwlen var (round*32+idx) ratio)
        with
        | e -> printfn "%A" split; reraise ()
    else None
) |> Array.append [|"dwlen,var,pos,ratio"|]
|> (fun x -> File.WriteAllLines(@"C:\Users\Yusuf Motara\Desktop\compressibility.csv", x))
*)
// TSV format: dwlen, var, position, ratio.
// I want to graph (x vs y):
// - dwlen vs ratio (averaged across all bitpos), with lines for each var.
// - bitpos vs ratio (averaged across all dwlen), with lines for each var.

open System.Collections.Generic

type ttCsv = CsvProvider< @"..\data\compressibility.csv" >

// dwlen vs ratio (averaged across all bitpos), with lines for each var.

open System.Drawing
let colors =
    ["A", Color.Red; "F", Color.HotPink; "W", Color.CornflowerBlue; "V0", Color.Gray; "V1", Color.Green]
    |> List.map (fun (k,v) -> k, Color.FromArgb(128, int v.R, int v.G, int v.B))
    |> Map.ofList

let cache = new Dictionary<_,_>()
let dwlenVsRatio v =
    if not <| cache.ContainsKey ("1"+v) then
        let d = new Dictionary<_,_>()
        for i = 1 to 24 do d.Add(i, new List<_>())
        ttCsv.GetSample().Rows
        |> Seq.toArray
        |> Array.filter (fun x -> x.Var = v && x.Dwlen >= 8 && x.Pos > 512)
        |> Array.iter (fun x -> 
            try
                d.[x.Dwlen].Add(float x.Ratio)
            with
            | _ ->
                eprintfn "Couldn't find %d key" x.Dwlen
                reraise ()
            )
        let tuples = d.Keys |> Seq.map (fun k -> k, d.[k].ToArray()) |> Seq.sortBy fst |> Seq.toArray
        cache.["1"+v] <- tuples
    Chart.BoxPlotFromData(cache.["1"+v], Name=sprintf "%s-values" v, ShowUnusualValues=false, ShowMedian=false, ShowAverage=false, WhiskerPercentile=10, Color=colors.[v])

// bitpos vs ratio (averaged across all dwlen)

let bitposVsRatio v =
    let median values =
        let sorted = Array.sort values
        let floor = sorted.Length/2
        if sorted.Length % 2 = 0 then (sorted.[floor] + sorted.[floor+1]) / 2.
        else sorted.[floor]
    if not <| cache.ContainsKey ("2"+v) then
        let d = new Dictionary<_,_>()
        //for i = 513 to 2570/2 do d.Add(i, new List<_>())
        ttCsv.GetSample().Rows
        |> Seq.toArray
        |> Array.filter (fun x -> x.Var = v && x.Dwlen >= 8 && x.Pos > 512 && x.Pos <= 2587)
        |> Array.iter (fun x ->
            let k = x.Pos
            if not <| d.ContainsKey k then d.Add(k, new List<_>())
            d.[k].Add(float x.Ratio)
        )
        let tuples = d.Keys |> Seq.map (fun k -> k, d.[k].ToArray()) |> Seq.sortBy fst |> Seq.toArray
        cache.["2"+v] <- tuples
    Chart.Line(cache.["2"+v] |> Array.map (fun (k,v) -> k,median v), Name=sprintf "%s-values" v, Color=colors.[v])

let baseline =
    Chart.Line([0,1.; 10000,1.], Name="Baseline")

let a_1 = dwlenVsRatio "A"
let w_1 = dwlenVsRatio "W"
let f_1 = dwlenVsRatio "F"
let v0_1 = dwlenVsRatio "V0"
let v1_1 = dwlenVsRatio "V1"

let ch1 =
    Chart.Combine([a_1;w_1;f_1;v0_1;v1_1;baseline])
        .WithLegend(Enabled=true)
        .WithYAxis(Max=1.3, Min= 0., MajorGrid=new ChartTypes.Grid(false), Title="Compression ratio")
        .WithXAxis(Max=24., Min=8., MajorGrid=new ChartTypes.Grid(false), Title="n")
        .WithTitle("Compression ratio with increasing values of n")

let a_2 = bitposVsRatio "A"
let w_2 = bitposVsRatio "W"
let f_2 = bitposVsRatio "F"
let v0_2 = bitposVsRatio "V0"
let v1_2 = bitposVsRatio "V1"

let ch2 =
    Chart.Combine([a_2;w_2;f_2;v0_2;v1_2;baseline])
        .WithLegend(Enabled=true)
        .WithYAxis(Min=0., Max=1.2, MajorGrid=new ChartTypes.Grid(false), Title="Median compression ratio")
        .WithXAxis(Min=513., Max=2587., MajorGrid=new ChartTypes.Grid(true, 256., 512., LineColor=Color.Transparent), Title="Bit-position")
        .WithTitle("Compression ratio as bit position increases")

let ch3 =
    Chart.Combine([a_2;w_2;f_2;v0_2;v1_2;baseline])
        .WithLegend(Enabled=true)
        .WithYAxis(Min=0., Max=1.2, MajorGrid=new ChartTypes.Grid(false), Title="Median compression ratio")
        .WithXAxis(Min=2427., Max=2587., MajorGrid=new ChartTypes.Grid(true, 256., 512., LineColor=Color.Transparent), Title="Bit-position")
        .WithTitle("Compression ratio as bit position increases")
