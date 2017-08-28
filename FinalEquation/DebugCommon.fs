namespace FinalEquation.Debugging
open FinalEquation.CommonStructure
open System.Collections.Generic

// this is a straight-up implementation that just uses bools everywhere.
// Useful for checking that the CommonStructure is doing what it should be doing.
// This should be lightning-fast and, ideally, this should NEVER go wrong.

type AbstractNode = Dictionary<uint32[],bool> * (uint32[] -> bool)

type PassThrough() =
    let eval (x : AbstractNode) =
        fun data ->
            let cache, func = x
            if cache.ContainsKey data then cache.[data]
            else
                cache.[data] <- func data
                cache.[data]
    interface IRepresentation<AbstractNode> with
        member __.And a b = new Dictionary<_,_>(), (fun data -> eval a data && eval b data)
        member __.Or a b = new Dictionary<_,_>(), (fun data -> eval a data || eval b data)
        member __.Xor a b = new Dictionary<_,_>(), (fun data -> eval a data <> eval b data)
        member __.Not x = new Dictionary<_,_>(), (fun data -> not (eval x data))
        member __.MakeVariable n = new Dictionary<_,_>(), (fun data -> data.[int n/32].[int n%32])
        member __.Evaluate data point = eval point data
        member __.EvaluationCache data = None
        member __.Constants with get () = { Zero=new Dictionary<_,_>(), (fun _ -> false); One=new Dictionary<_,_>(), (fun _ -> true) }
        member __.IsOne ( (_,x) ) = x Array.empty = true
        member __.IsZero ( (_,x) ) = x Array.empty = false
        member __.Dispose () = ()
