namespace FinalEquation.CommonStructure.Storage

open FinalEquation.CommonStructure

// this kind of storage will write everything to disk if it feels that it's running out of RAM.
// It also ignores the DWLen.
type MemoryStorage<'T>() =
    let tags = System.Collections.Concurrent.ConcurrentDictionary<Designator, 'T>()

    let get key =
        let o =
            try tags.[key] with
            | _ ->
                eprintfn "Looked for, but didn't find, %A" key
                reraise ()
        o

    let getOrGenerate (key : Designator) f =
        let o = tags.GetOrAdd(key, fun _ -> f key)
        o
        
    let exists (key : Designator) : bool =
        let ret = tags.ContainsKey key
        //if not ret then System.Console.WriteLine("Key {0} does not exist.", key)
        ret

    let store (key : Designator) (item : 'T) =
        //System.Console.WriteLine("Storing: {0}", key)
        tags.[key] <- item

    let delete =
        let dummy = ref Unchecked.defaultof<'T>
        fun (key : Designator) -> tags.TryRemove(key, dummy) |> ignore

    let deleteAllExcept f =
        let keys = tags.Keys |> Seq.toArray
        for k in keys do
            if not (f k) then delete k
    
    let storeINE (key : Designator) item = 
        if not <| exists key then store key item

    interface IStorage<'T> with
        member __.Get x = get x
        member __.GetOrGenerate k f = getOrGenerate k f
        member __.Item x = get x
        member __.Store key value = store key value
        member __.StoreINE key value = storeINE key value
        member __.Delete key = delete key
        member __.DeleteAllExcept filter = deleteAllExcept filter
        member __.Clear () = deleteAllExcept (fun _ -> false)
        member __.Exists key = exists key
        member __.ToSecondaryStorage () = printfn "ToSecondaryStorage() is a no-op for MemoryStorage"
        member __.FromSecondaryStorage () = printfn "FromSecondaryStorage() is a no-op for MemoryStorage"