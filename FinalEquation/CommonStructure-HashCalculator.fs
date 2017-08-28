[<AutoOpen>]
module FinalEquation.CommonStructure.HashCalculation

open FinalEquation
open FinalEquation.CommonStructure.SubCalculations
open FinalEquation.CommonStructure.Utilities

type HashCalculator<'T>(dwlen : uint32, repr : IRepresentation<'T>, storage : IStorage<'T>, subcalcs : ISubCalculator<'T>) = 
    //let subcalcs = SubCalculations(dwlen, w, Never, repr, storage)
    let mutable killOrder = false // when set to true, kills unneeded things after all generation is complete
                
    let accumulate_logic_calculations () =         
        let sw = new System.Diagnostics.Stopwatch()
        
        for (r, i) in bitProgression (1, 26) 81 do
            if i = 26 then
                if sw.ElapsedMilliseconds > 300L then
                    System.Console.WriteLine("r.{0} start", r)
                sw.Restart()
            let target = { Round=r; Bit=i; Var=V.A }
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_overall target
            // subcalculate each of the dependencies explicitly
            ignore <| subcalcs.[akey]
            ignore <| subcalcs.[fkey]
            ignore <| subcalcs.[ekey]
            ignore <| subcalcs.[wkey]
            if Option.isSome v0key then ignore <| subcalcs.[Option.get v0key]
            if Option.isSome v1key then ignore <| subcalcs.[Option.get v1key]
            // the final output for this (r,i) combination
            ignore <| subcalcs.[target]
            //storage.Store key out
            //System.Console.Write("R({0},{1})", r, i)

    member __.GenerateRepresentation () =
        accumulate_logic_calculations ()
        if killOrder then
            storage.DeleteAllExcept (fun (k : Designator) -> k.Var = V.A && k.Round >= 76)
            storage.ToSecondaryStorage ()
    member __.DeleteNonFinal with set v = killOrder <- v
    member __.VerifyRepresentation () = verify dwlen repr storage 81
