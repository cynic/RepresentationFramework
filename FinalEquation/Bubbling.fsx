#load "Dependencies.fsx"
#load "AIG.fs"
#load "AIG-Bobbling.fs"

open FinalEquation
open FinalEquation.CommonStructure
open FinalEquation.AIG
open FinalEquation.AIG.Bobbling

let make_test_aiger dwlen =
    let o = new AndInverterGraph(dwlen)
    let r = o :> IRepresentation<_>
    let s = Storage.DiskStorage(dwlen, r) :> IStorage<_>
    let words = Words.BaseXor(dwlen, r, s)
    let subcalcs = SubCalculations.AndOrXorNot(dwlen, words, SubCalcRecursion.Always, r, s)
    let h = HashCalculator<_>(dwlen, r, s, subcalcs)

    h.GenerateRepresentation ()

    let preimageOutput =
        let output, input =
            match dwlen with
            | 3u -> "e3eee297aa09a22655a858cced91f6282bde72ce", "af"
            | 6u -> "261f6b322cb0ca9eabc2ea17d0211af21dd90720", "ac"
            | 8u -> "3c710d3603e92bc62c2c38714caa691a6ab69b2d", "de"
            | 10u -> "cf6b04eb0fa6a2cb006507d7b0ae78eeb787726f", "dead"
            | 12u -> "64221578fc4e66a5224a199e8a952faddbdffb6b", "dead"
            | 14u -> "1b40dc3785febb7f1401c03d3ff2f2608454af2f", "dead"
            | 16u -> "b1fef21c7d8753f899e4ba14268b169b7b451adc", "dead"
            | 24u -> "a79a832e7d1b471f27893177c7c6bcdbdfa089f6", "deadbe"
            | 32u -> "704a68b8a2d7bed0e6b19d21a8e66702634085fb", "deadbeef"
            | 64u -> "c9176211c8b091deaf915c3720c4e9260e78cf0a", "deadbeefcafeb4be"
            | 96u -> "2c0257f8264910d27729d68ad1ee86d6aa9e3cf3", "deadbeefcafeb4beabad1dea"
            | 128u -> "8d738caaed10771cfebd6067adf9d5759e715989", "deadbeefcafeb4beabad1dea12345678"
            | 192u -> "7063467c1b834662abc76b16a5cfc7aabd8e084f", "deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d"
            | 256u -> "da2d58e37c2e736bf94056e518e99d3347bdce11", "deadbeefcafeb4beabad1dea123456789abcdef0b33fd00d261f6b327e27c2ad"
        let calc = PreimageCalculator(r, input, s, dwlen)
        if calc.ExpectedOutput <> output then failwith "Error in input/output matching"
        calc.SingleEquationForm()

    // now for the CleanStar stuff.

    let abc = ABCInterface(dwlen)
    let aag = { AAG.Ands=o.AAG.Ands; AAG.Output=o.AAG.Output }
    //abc.WriteAiger(aag, sprintf @"P:\%d.aig" dwlen)
    //let strashed = abc.AIGEvaluate(aag, ABCOp.Strash)
    //abc.WriteAiger(aag, sprintf @"P:\%d_strashed.aig" dwlen)
    //let min = abc.AIGEvaluate(aag, ABCOp.Minimise)
    //abc.WriteAiger(aag, sprintf @"P:\%d_min.aig" dwlen)
    abc, aag

System.Environment.CurrentDirectory <- __SOURCE_DIRECTORY__
open System.IO

let debug_problem () =
    let abc = ABCInterface(6u)
    let aag = abc.ReadAiger(@"P:\output_3\file_2_out.aig")
    abc.WriteAiger(aag, @"C:\temp\a.aig")
    // now, post-bubbling file_2 is NOT equivalent to pre-bubbling file_2.
    // I need to understand why... :-(
    // Possibilities:
    // - My code is fine, and the problem is the strashing at the end of bubbling.  Unlikely, but check first.
    //   - NO. Checked by looking at the original & the pre-strashed; pre-strashed is messed-up.
    // - There's a problem with my code - must figure out where, though.  Likely areas:
    //   - patching?
    // Whatever it is, it's related to index 18:
(*
===CEC OUTPUT BEGIN
ABC command line: "read_aiger C:\Temp\output_6\file_37.aig; cec C:\Temp\output_6\file_38.aig".

Loading resource file "abc.rc".
Networks are NOT EQUIVALENT.
Verification failed for at least 1 outputs:  po0
Output po0: Value in Network1 = 1. Value in Network2 = 0.
Input pattern:  pi0=1 pi2=1 pi1=0

===CEC OUTPUT END
System.Exception: ERROR - NOT equivalent after modification of index 18
*)
    let newaag = bubbleOut 6u 2u aag
    abc.WriteAiger(aag, @"C:\temp\b.aig")
    if not <| abc.AIGEquivalent(aag, newaag) then failwith "No."

//let aag = abc.ReadAiger(@"c:\temp\to_bubble.aig")
//let new_aag = bubbleOut 6u 3u aag

//let abc, aag = make_test_aiger 8u
//#time
//let new_aag = bubbleOut 8u 1u aag

let macross () =
    for dwlen in [(*3u;6u;8u;*)10u;12u;14u;16u;24u] do
        let abc, aag = make_test_aiger dwlen
        let sw = System.Diagnostics.Stopwatch()
        let mutable optim = Unchecked.defaultof<AAG>
        for i = 1 to int dwlen do
            let to_bubble = if i = 1 then aag else optim
            abc.WriteAiger(to_bubble, sprintf @"c:\temp\%d_var_%d.aig" dwlen i)
            sw.Restart ()
            let bubbled = bubbleOut dwlen (uint32 i) to_bubble
            let tm_bubbled = sw.ElapsedMilliseconds
            abc.WriteAiger(bubbled, sprintf @"c:\temp\%d_var_%d_bubbled.aig" dwlen i)
            sw.Restart ()
            optim <-
                let test =
                    match abc.AIGEvaluate(bubbled, ABCOperation.MinimiseX) with
                    | Some v -> v
                    | None ->
                        printfn "MinimiseX *failed*.  Resetting optimization timer (was %d), trying MinimiseY." sw.ElapsedMilliseconds
                        sw.Restart ()
                        match abc.AIGEvaluate(bubbled, ABCOperation.MinimiseY) with
                        | Some v -> v
                        | None ->
                            printfn "MinimiseY also failed!  Oh, well....."
                            bubbled
                sw.Stop ()
                if test.Ands.Length = 0 then
                    printfn "Minimization messed up!  Or, did I mess up?!  Checking equivalence via CEC."
                    if abc.AIGEquivalent(bubbled, to_bubble) then
                        printfn "MY stuff is OK, the ABC stuff is messed up."
                        bubbled
                    else
                        printfn "The ABC stuff is OK, MY stuff is messed up."
                        to_bubble
                else test
            let tm_optim = sw.ElapsedMilliseconds
            using (File.AppendText(sprintf @"P:\aig_stats_%d.dat" dwlen)) (fun sw ->
                sw.WriteLine("{0} {1} {2} {3} {4}", i, bubbled.Ands.Length, optim.Ands.Length, tm_bubbled, tm_optim)
            )
            printfn "AIG-%d: %d done, min=%d. TM=%d, optimTM=%d" dwlen i optim.Ands.Length tm_bubbled tm_optim
