module FinalEquation.Tests

open FinalEquation.CommonStructure
open NUnit.Framework
open FsUnit

type TestData () =
    static member aig_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u;9u;10u;11u;12u;13u;14u;15u;16u;32u;64u;128u;256u;400u|]
    static member debug_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u;9u;10u;11u;12u;13u;14u;15u;16u;32u;64u;128u;256u;400u|]
    static member dnf_n = [|0u;1u;2u;3u;4u;5u(*;6u;7u;8u;9u;10u;11u;12u;13u;14u;15u;16u*)|]
    static member tt_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u;9u;10u;11u;12u;13u;14u;15u;16u;17u(*;18u;19u;20u;21u;22u;23u;24u*)|]
    static member cnf_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u;9u;10u;11u;12u;13u;14u;15u;16u;32u;64u;128u;256u;400u|]
    static member bdd_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u;10u|]
    static member mybdd_n = [|0u;1u;2u;3u;4u;5u;6u;7u;8u|]
    
    static member preimageEqn_data : obj[][] =
        [|
            // dwlen * output * input
            [|2u; "71c10ea23fe185e1eefe7b2dea1bb12cb35d23da"; "ff"|]
            [|3u; "e3eee297aa09a22655a858cced91f6282bde72ce"; "af"|]
            [|6u; "261f6b322cb0ca9eabc2ea17d0211af21dd90720"; "ac"|]
            [|32u; "704a68b8a2d7bed0e6b19d21a8e66702634085fb"; "deadbeef"|]
            [|64u; "c9176211c8b091deaf915c3720c4e9260e78cf0a"; "deadbeefcafeb4be"|]
            [|96u; "2c0257f8264910d27729d68ad1ee86d6aa9e3cf3"; "deadbeefcafeb4beabad1dea"|]
            [|128u; "8d738caaed10771cfebd6067adf9d5759e715989"; "deadbeefcafeb4beabad1dea12345678"|]
            [|192u; "7063467c1b834662abc76b16a5cfc7aabd8e084f"; "deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d"|]
            [|256u; "da2d58e37c2e736bf94056e518e99d3347bdce11"; "deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d261f6b327e27c2ad"|]
        |]

[<TestFixture>]
module Tests =
    let ``f-calculation test`` name f target =
        use oActual = new Debugging.PassThrough()
        let rActual = oActual :> IRepresentation<_>
        let sActual = Storage.DiskStorage<_>(3u) :> IStorage<_>
        let w = Words.BaseXor(3u, rActual, sActual) :> IWords<_>
        let sc =
            //SubCalculations.AndOrXorNot(3u, w, SubCalcRecursion.Always, rActual, sActual) :> ISubCalculator<_>
            SubCalculations.XorAnd(3u, w, SubCalcRecursion.Always, rActual, sActual) :> ISubCalculator<_>

        use oExpected = new Debugging.PassThrough()
        let rExpected = oExpected :> IRepresentation<_>
        let sExpected = Storage.DiskStorage<_>(3u) :> IStorage<_>

        // because of how PassThrough is implemented, this should work for both.
        let vx = rActual.MakeVariable 0u
        let vy = rActual.MakeVariable 1u
        let vz = rActual.MakeVariable 2u

        let data = [|
            [|0u|]; [|0x20000000u|]; [|0x40000000u|]; [|0x60000000u|]
            [|0x80000000u|]; [|0xa0000000u|]; [|0xc0000000u|]; [|0xe0000000u|]
        |]

        // right!  let's check.
        let ft = ["0",rActual.Constants.Zero; "1",rActual.Constants.One; "v0",vx; "v1",vy; "v2",vz]
        for dB,_b in ft do
            for dC,_c in ft do
                for dD,_d in ft do
                    printfn "Evaluating: %s(%s, %s, %s)" name dB dC dD
                    sActual.Delete target
                    sExpected.Delete target
                    let b,c,d = Keys.inputKeys_f target
                    sActual.Store b _b; sExpected.Store b _b
                    sActual.Store c _c; sExpected.Store c _c
                    sActual.Store d _d; sExpected.Store d _d
                    let v = f rExpected _b _c _d
                        //r.Or (r.And _c _d) (r.Or (r.And _b _c) (r.And _b _d))
                        //rExpected.Or (rExpected.And _b _c) (rExpected.And (rExpected.Not _b) _d)
                    let v' = sc.F target
                    // now evaluate.
                    for x in data do
                        let actual = rActual.Evaluate x v'
                        let expected = rExpected.Evaluate x v
                        actual |> should equal expected
                    printfn "Pass."

    [<Test>]
    let ``f-calculation test (choice)`` () =
        ``f-calculation test`` "CHOICE" (fun r b c d -> r.Or (r.And b c) (r.And (r.Not b) d)) ({ Round=10; Bit=0; Var=V.F })

    [<Test>]
    let ``f-calculation test (parity)`` () =
        ``f-calculation test`` "PARITY" (fun r b c d -> r.Xor (r.Xor b c) d) ({ Round=70; Bit=0; Var=V.F })

    [<Test>]
    let ``f-calculation test (majority)`` () =
        ``f-calculation test`` "MAJORITY" (fun r b c d -> r.Or (r.And c d) (r.Or (r.And b c) (r.And b d))) ({ Round=50; Bit=0; Var=V.F })

    let basicLogicTests (mkRepr : unit -> #IRepresentation<_>) =
        let binaryLogic opName logicOp reprOp (repr : IRepresentation<_>) =
            let result a b = logicOp a b
            let _0, _1 = repr.Constants.Zero, repr.Constants.One
            let combinations =
                [|
                    false, false, _0, _0
                    false, true, _0, _1
                    true, false, _1, _0
                    true, true, _1, _1
                |]
            for (a,b,x,y) in combinations do
                let expected = result a b
                let actual = reprOp x y
                let msg () = sprintf "Incorrect evaluation of (%b %s %b)" a opName b
                if expected then Assert.AreEqual(true, repr.IsOne actual, msg ())
                else Assert.AreEqual(false, not (repr.IsZero actual), msg ())
                let msg () = sprintf "Incorrect evaluation of (NOT (%b %s %b))" a opName b
                let not_actual = repr.Not actual
                if not expected then Assert.AreEqual(true, repr.IsOne not_actual, msg ())
                else Assert.AreEqual(false, not (repr.IsZero not_actual), msg ())
        let unaryLogic (repr : IRepresentation<_>) =
            let expect_zero = repr.Not(repr.Constants.One)
            Assert.IsTrue(repr.IsZero expect_zero, "Incorrect evaluation of NOT(True)")
            let expect_one = repr.Not(repr.Constants.Zero)
            Assert.IsTrue(repr.IsOne expect_one, "Incorrect evaluation of NOT(False)")
        using (mkRepr()) (fun repr -> unaryLogic repr)
        using (mkRepr()) (fun repr -> binaryLogic "AND" (&&) repr.And repr)
        using (mkRepr()) (fun repr -> binaryLogic "OR" (||) repr.Or repr)
        using (mkRepr()) (fun repr -> binaryLogic "XOR" (<>) repr.Xor repr)

    let do_test name n mkRepr =
        let do_test_using_wMethod mkW repr =
            let storage = Storage.DiskStorage<_>(n) :> IStorage<_>
            let w = mkW storage :> IWords<_>
            let sc =
                //SubCalculations.AndOrXorNot(n, w, Never, repr, storage)
                SubCalculations.XorAnd(n, w, Never, repr, storage)
            let calc = HashCalculator(n, repr, storage, sc)
            let sw = System.Diagnostics.Stopwatch()
            System.Console.WriteLine("{0} {1}: length {2}", string w, name, n)
            sw.Start()
            calc.GenerateRepresentation()
            sw.Stop()
            System.Console.WriteLine("{0} {1} representation generated in {2}", string w, name, sw.Elapsed)
            sw.Restart()
            calc.VerifyRepresentation ()
            sw.Stop()
            System.Console.WriteLine("{0} {1} verified in {2}", string w, name, sw.Elapsed)
            storage.Clear ()
        using (mkRepr ()) (fun repr -> do_test_using_wMethod (fun s -> Words.Traditional(n, repr, s)) repr)
        using (mkRepr ()) (fun repr -> do_test_using_wMethod (fun s -> Words.BaseXor(n, repr, s)) repr)

    [<Test>]
    let ``Basic logic: CommonStructure verification`` () = basicLogicTests (fun () -> new Debugging.PassThrough ())

    [<Test;TestCaseSource(typeof<TestData>, "debug_n") >]
    let ``CommonStructure verification`` n = do_test "CommonStructure" n (fun () -> new Debugging.PassThrough ())

    [<Test;TestCaseSource(typeof<TestData>, "preimageEqn_data")>]
    let ``PreimageEquation verification`` (dwlen, output, input) =
        use repr = new Debugging.PassThrough () :> IRepresentation<_>
        let storage = Storage.DiskStorage<_>(dwlen) :> IStorage<_>
        let w = Words.BaseXor(dwlen, repr, storage)
        let sc =
            //SubCalculations.AndOrXorNot(dwlen, w, Never, repr, storage)
            SubCalculations.XorAnd(dwlen, w, Never, repr, storage)
        let calc = HashCalculator(dwlen, repr, storage, sc)
        calc.GenerateRepresentation ()
        let pie = PreimageCalculator(repr, input, storage, dwlen)
        System.Console.WriteLine("Expected output is:\n{0}\n{1}", pie.ExpectedOutput, output)
        let sef = pie.SingleEquationForm ()
        // now, when evaluated with /input/, /sef/ should be 1
        let input =
            let bytes = Utilities.hexstringToBytes input |> Option.get
            Utilities.bytesToHashInput bytes (int dwlen)
(* // debugging
        seq {
            for n = 0 to 159 do
                let key = Utilities.hashDesignator dwlen n
                let point = storage.[key]
                if repr.Evaluate input point then yield 1uy
                else yield 0uy
        } |> Seq.chunkBySize 32 |> Seq.map Utilities.bitsToWord
        |> Seq.map (sprintf "%08x")
        |> String.concat "" |> System.Console.WriteLine
*)
        let result = repr.Evaluate input sef
        Assert.IsTrue(result)
        
    [<Test>]
    let ``Basic logic: And-Inverter Graph`` () = basicLogicTests (fun () -> new AIG.AndInverterGraph(4u))

    [<Test;TestCaseSource(typeof<TestData>, "aig_n") >]
    let ``And-Inverter Graph verification`` n = do_test "AIG" n (fun () -> new AIG.AndInverterGraph(n))

    [<Test>]
    let ``Basic logic: Disjunctive Normal Form`` () = basicLogicTests (fun () -> new DNF.DisjunctiveNormalForm())

    [<Test;TestCaseSource(typeof<TestData>, "dnf_n") >]
    let ``Disjunctive Normal Form verification`` n = do_test "DNF" n (fun () -> new DNF.DisjunctiveNormalForm ())

    [<Test>]
    let ``Basic logic: Truth Table`` () = basicLogicTests (fun () -> new TruthTables.BitArrays.TruthTable(4u))

    [<Test;TestCaseSource(typeof<TestData>, "tt_n") >]
    let ``Truth Table verification`` n = do_test "Truth Table" n (fun () -> new TruthTables.BitArrays.TruthTable(n))

    [<Test>]
    let ``Basic logic: Conjunctive Normal Form`` () = basicLogicTests (fun () -> new CNF.Tseitin.ConjunctiveNormalForm(4u))

    [<Test;TestCaseSource(typeof<TestData>, "cnf_n")>]
    let ``Conjunctive Normal Form verification`` n = do_test "CNF (via Tseitin)" n (fun () -> new CNF.Tseitin.ConjunctiveNormalForm(n))

    [<Test>]
    let ``Basic logic: Binary Decision Diagram [external]`` () = basicLogicTests (fun () -> new BDD.BinaryDecisionDiagram(4u))

    [<Test;TestCaseSource(typeof<TestData>, "bdd_n")>]
    let ``Binary Decision Diagram [external] verification`` n = do_test "BDD" n (fun () -> new BDD.BinaryDecisionDiagram(n))

    [<Test>]
    let ``Basic logic: Binary Decision Diagram [mine]`` () = basicLogicTests (fun () -> new MyBDD.BinaryDecisionDiagram(4u))

    [<Test;TestCaseSource(typeof<TestData>, "mybdd_n")>]
    let ``BinaryDecision Diagram [mine] verification`` n = do_test "MyBDD" n (fun () -> new MyBDD.BinaryDecisionDiagram(n))
