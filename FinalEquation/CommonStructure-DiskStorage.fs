namespace FinalEquation.CommonStructure.Storage

open FinalEquation.CommonStructure

// this kind of storage will write everything to disk if it feels that it's running out of RAM.

type DiskStorage<'T>(dwlen) =
    let path =
        let p = @"c:\temp\repr_pickling"
        System.IO.Directory.CreateDirectory p |> ignore
        p
    let reprName = typeof<'T>.Name

    let tags = System.Collections.Concurrent.ConcurrentDictionary<Designator, Option<'T>>()

    let diskify () =
        lock (tags) (fun () ->
            let keys = Seq.toArray tags.Keys
            for k in keys do
                match tags.[k] with
                | Some o ->
                    let path = System.IO.Path.Combine(path, reprName + string k)
                    if not <| System.IO.File.Exists path then
                        let pickler = Nessos.FsPickler.BinarySerializer()
                        using (System.IO.File.Create path) (fun fs ->
                            pickler.Serialize(fs, o)
                        )
                    tags.[k] <- None
                | None -> ()
        )

    let undiskify () = // push from disk to tags.
        for var in [V.A; V.F; V.V0; V.W; V.V1] do
            for round = 1 to 80 do
                for bit = 0 to 31 do
                    let key = { Round=round; Bit=bit; Var=var }
                    let path = System.IO.Path.Combine(path, reprName + string key)
                    if System.IO.File.Exists path then tags.[key] <- None

    let memLimit =
        if not <| System.Environment.Is64BitProcess then 1024L*1024L*1200L // ~1.2Gib
        else 1024L*1024L*1024L*9L // ~9GiB

    let diskify_if_necessary key =
        let taken = System.GC.GetTotalMemory false
        if taken >= memLimit then
            printfn "@ %O.  Taking up too much memory (~%fMiB)!  Serializing to disk." key (float taken / 1024. / 1024.)
            let sw = System.Diagnostics.Stopwatch.StartNew()
            diskify ()
            sw.Stop()
            System.GC.Collect()
            let newTaken = System.GC.GetTotalMemory true
            printfn "Now taking up ~%fMiB. Serialization took %O." (float newTaken / 1024. / 1024.) sw.Elapsed

    let get key =
        diskify_if_necessary key
        let o =
            try
                match tags.[key] with
                | Some o -> o
                | None ->
                    let path = System.IO.Path.Combine(path, reprName + string key)
                    let pickler = Nessos.FsPickler.BinarySerializer()
                    let o = pickler.Deserialize<'T>(System.IO.File.OpenRead path)
                    tags.[key] <- Some o
                    o
            with
            | _ ->
                eprintfn "Looked for, but didn't find, %A" key
                reraise ()
        o

    let getOrGenerate (key : Designator) f =
        diskify_if_necessary key
        let o =
            match tags.GetOrAdd(key, fun _ -> Some ( f key )) with
            | Some o -> o
            | None ->
                let path = System.IO.Path.Combine(path, reprName + string key)
                let pickler = Nessos.FsPickler.BinarySerializer()
                let o = pickler.Deserialize<'T>(System.IO.File.OpenRead path)
                tags.[key] <- Some o
                o
        o
        
    let exists (key : Designator) : bool =
        let ret = tags.ContainsKey key
        //if not ret then System.Console.WriteLine("Key {0} does not exist.", key)
        ret

    let store (key : Designator) (item : 'T) =
        //System.Console.WriteLine("Storing: {0}", key)
        tags.[key] <- Some item

    let delete (key : Designator) =
        if tags.ContainsKey key then
            let dummy = ref None
            //System.Console.WriteLine("Deleting: {0}", key)
            tags.TryRemove(key, dummy) |> ignore
            let path = System.IO.Path.Combine(path, reprName + string key)
            System.IO.File.Delete path

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
        member __.ToSecondaryStorage () = diskify ()
        member __.FromSecondaryStorage () = undiskify ()