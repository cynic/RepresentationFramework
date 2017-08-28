namespace FinalEquation.CommonStructure.SubCalculations

open FinalEquation.CommonStructure

module Internal =
    let init_subcalc_constants (storage : IStorage<_>) (repr : IRepresentation<_>) =
        /// Left-rotate /i/ by /n/
        let inline (<<<<) (i : uint32) n = i <<< n ||| (i >>> (32-n))
        let rot0 = Constants.H0 <<<< 5 // 0xe8a4602cu
        let rot1 = Constants.H1 <<<< 5 // 0xf9b5713du
        let rot2 = Constants.H2 <<<< 7 // 0x5d6e7f4cu
        let rot3 = Constants.H3 <<<< 7 // 0x192a3b08u
        let rot4 = Constants.H4 <<<< 7 // 0xe970f861u
        let ifset x = if x then repr.Constants.One else repr.Constants.Zero
        for i = 0 to 31 do
            storage.StoreINE ({ Round=0; Bit=i; Var=V.A }) (ifset rot0.[i])
            storage.StoreINE ({ Round= -1; Bit=i; Var=V.A }) (ifset rot1.[i])
            storage.StoreINE ({ Round= -2; Bit=i; Var=V.A }) (ifset rot2.[i])
            storage.StoreINE ({ Round= -3; Bit=i; Var=V.A }) (ifset rot3.[i])
            storage.StoreINE ({ Round= -4; Bit=i; Var=V.A }) (ifset rot4.[i])
            storage.StoreINE ({ Round=0; Bit=i; Var=V.F }) (ifset 0x98badcfeu.[i])
            storage.StoreINE ({ Round=1; Bit=i; Var=V.F }) (ifset 0xfbfbfefeu.[i])
        for p = 0 to 80 do
            storage.StoreINE ({ Round=p; Bit=26; Var=V.V0 }) repr.Constants.Zero
            storage.StoreINE ({ Round=p; Bit=26; Var=V.V1 }) repr.Constants.Zero
            storage.StoreINE ({ Round=p; Bit=25; Var=V.V1 }) repr.Constants.Zero

    let redirect (this : ISubCalculator<_>) (storage : IStorage<_>) =
        fun (key : Designator) ->
            storage.GetOrGenerate key (fun key ->
                match key.Var with
                | V.W -> this.W key
                | V.A -> this.A key
                | V.F -> this.F key
                | V.V0 -> this.V0 key
                | V.V1 -> this.V1 key
                | _ -> failwithf "Invalid Var value %A" key.Var
            )

    let alwaysRecurse (storage : IStorage<_>) redirect =
        { new IStorage<'T> with
            member __.Get x = redirect x
            member __.GetOrGenerate a b = storage.GetOrGenerate a b
            member __.Item x = redirect x
            member __.Store a b = storage.Store a b
            member __.StoreINE a b = storage.StoreINE a b
            member __.Delete x = storage.Delete x
            member __.DeleteAllExcept f = storage.DeleteAllExcept f
            member __.Clear () = storage.Clear ()
            member __.Exists k = storage.Exists k
            member __.ToSecondaryStorage () = storage.ToSecondaryStorage ()
            member __.FromSecondaryStorage () = storage.FromSecondaryStorage ()
        }

    let neverRecurse (storage : IStorage<_>) = storage

    let sometimesRecurse (storage : IStorage<_>) (w : IWords<_>) dwlen redirect f =
        let varCoalesce = System.Collections.Generic.Dictionary()
        let aCalc_lookup =
            Utilities.bitProgression (1,26) 81
            |> Seq.rev |> Seq.collect (fun (p,i) ->
                let a,f,e,w,v0,v1 = Keys.inputKeys_overall ({ Round=p; Bit=i; Var=V.A })
                //let f_b, f_c, f_d = Keys.inputKeys_f f
                seq {
                    yield a,(p,i)
                    yield f,(p,i)
                    //yield f_b,(p,i)
                    //yield f_c,(p,i)
                    //yield f_d,(p,i)
                    yield e,(p,i)
                    yield w,(p,i)
                    if v0.IsSome then yield (Option.get v0),(p,i)
                    if v1.IsSome then yield (Option.get v1),(p,i)
                }
            ) |> Seq.toArray
        let checkRecursion x =
            // right.  FIRST, I need to check whether I should be interested in
            // replacing this var at all.
            // THEN, if I am interested, I should figure out whether I need a new
            // var, or if I already have one which will do just fine.
                match f x with
                | Yes ->
                    //printfn "Got a YES/DESCEND response for designator %s" x.S
                    redirect x
                //| No -> storage.Get x
                | InsteadUse vf ->
                    let aCalc = aCalc_lookup |> Array.find (fun (y,_) -> y = x) |> snd
                    match varCoalesce.TryGetValue aCalc with
                    | true, v ->
                        //printfn "Replaced %s with existing dVar for %A" x.S aCalc
                        v
                    | _ ->
                        //printfn "Got an INSTEAD response for designator %s, storing into %A & returning." x.S aCalc
                        let v = vf ()
                        varCoalesce.[aCalc] <- v
                        v
            // let's try to get a good idea of where this key is coming from.
        let get (x : Designator) =
            if x.Var = V.W then
                if storage.Exists x then storage.Get x
                else w.Word x
            elif storage.Exists x then
                //printfn "Expanding: %s" x.S
                storage.Get x
            else checkRecursion x
        { new IStorage<'T> with
            member __.Get x = get x
            member __.GetOrGenerate a b = storage.GetOrGenerate a b
            member __.Item x = get x
            member __.Store a b = storage.Store a b
            member __.StoreINE a b = storage.StoreINE a b
            member __.Delete x = storage.Delete x
            member __.DeleteAllExcept f = storage.DeleteAllExcept f
            member __.Clear () = storage.Clear ()
            member __.Exists k = storage.Exists k
            member __.ToSecondaryStorage () = storage.ToSecondaryStorage ()
            member __.FromSecondaryStorage () = storage.FromSecondaryStorage ()
        }
