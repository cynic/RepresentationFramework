namespace FinalEquation.CommonStructure.SubCalculations

open FinalEquation.CommonStructure

// doesn't matter which kind of /IWords<'T>/ is supplied, they both use XOR exclusively.
type XorAnd<'T>(dwlen : uint32, w : IWords<'T>, recurse, repr : IRepresentation<'T>, storage : IStorage<'T>) as __ =
    do
        Internal.init_subcalc_constants storage repr

    let redirect = Internal.redirect __ storage

    let storage =
        match recurse with
        | Always -> Internal.alwaysRecurse storage redirect
        | Never -> Internal.neverRecurse storage
        | Depends f -> Internal.sometimesRecurse storage w dwlen redirect f
            
    let (&&&) a b = repr.And a b
    let (^^^) a b = repr.Xor a b

    (* // via SAGE, see Script.fsx
sage: B_1256_6.algebraic_normal_form()
(a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a &&& v0) ^^^ (a &&& v1) ^^^ (a) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (f &&& v0) ^^^ (f &&& v1) ^^^ (f) ^^^ (e &&& w) ^^^ (e &&& v0) ^^^ (e &&& v1) ^^^ (e) ^^^ (w &&& v0) ^^^ (w &&& v1) ^^^ (w) ^^^ (v0 &&& v1) ^^^ (v0) ^^^ (v1)
sage: B_236_6.algebraic_normal_form()
(a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a &&& v0) ^^^ (a &&& v1) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (f &&& v0) ^^^ (f &&& v1) ^^^ (e &&& w) ^^^ (e &&& v0) ^^^ (e &&& v1) ^^^ (w &&& v0) ^^^ (w &&& v1) ^^^ (v0 &&& v1)
sage: B_3456_6.algebraic_normal_form()
(a &&& f &&& e &&& w) ^^^ (a &&& f &&& e &&& v0) ^^^ (a &&& f &&& e &&& v1) ^^^ (a &&& f &&& e) ^^^ (a &&& f &&& w &&& v0) ^^^ (a &&& f &&& w &&& v1) ^^^ (a &&& f &&& w) ^^^ (a &&& f &&& v0 &&& v1) ^^^ (a &&& f &&& v0) ^^^ (a &&& f &&& v1) ^^^ (a &&& e &&& w &&& v0) ^^^ (a &&& e &&& w &&& v1) ^^^ (a &&& e &&& w) ^^^ (a &&& e &&& v0 &&& v1) ^^^ (a &&& e &&& v0) ^^^ (a &&& e &&& v1) ^^^ (a &&& w &&& v0 &&& v1) ^^^ (a &&& w &&& v0) ^^^ (a &&& w &&& v1) ^^^ (a &&& v0 &&& v1) ^^^ (f &&& e &&& w &&& v0) ^^^ (f &&& e &&& w &&& v1) ^^^ (f &&& e &&& w) ^^^ (f &&& e &&& v0 &&& v1) ^^^ (f &&& e &&& v0) ^^^ (f &&& e &&& v1) ^^^ (f &&& w &&& v0 &&& v1) ^^^ (f &&& w &&& v0) ^^^ (f &&& w &&& v1) ^^^ (f &&& v0 &&& v1) ^^^ (e &&& w &&& v0 &&& v1) ^^^ (e &&& w &&& v0) ^^^ (e &&& w &&& v1) ^^^ (e &&& v0 &&& v1) ^^^ (w &&& v0 &&& v1)
sage: B_456_6.algebraic_normal_form()
(a &&& f &&& e &&& w) ^^^ (a &&& f &&& e &&& v0) ^^^ (a &&& f &&& e &&& v1) ^^^ (a &&& f &&& w &&& v0) ^^^ (a &&& f &&& w &&& v1) ^^^ (a &&& f &&& v0 &&& v1) ^^^ (a &&& e &&& w &&& v0) ^^^ (a &&& e &&& w &&& v1) ^^^ (a &&& e &&& v0 &&& v1) ^^^ (a &&& w &&& v0 &&& v1) ^^^ (f &&& e &&& w &&& v0) ^^^ (f &&& e &&& w &&& v1) ^^^ (f &&& e &&& v0 &&& v1) ^^^ (f &&& w &&& v0 &&& v1) ^^^ (e &&& w &&& v0 &&& v1)
sage: B_12_4.algebraic_normal_form()
(a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (f) ^^^ (e &&& w) ^^^ (e) ^^^ (w)
sage: B_23_4.algebraic_normal_form()
(a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (e &&& w)
sage: B_34_4.algebraic_normal_form()
(a &&& f &&& e &&& w) ^^^ (a &&& f &&& e) ^^^ (a &&& f &&& w) ^^^ (a &&& e &&& w) ^^^ (f &&& e &&& w)
sage: B_4_4.algebraic_normal_form()
a &&& f &&& e &&& w
    *)

    let v0_12_4 (t : Designator) : 'T = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        (a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (f) ^^^ (e &&& w) ^^^ (e) ^^^ (w) // 10 terms, degree 2
    
    let v0_23_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        (a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (f &&& e) ^^^ (f &&& w) ^^^ (e &&& w) // 6 terms, degree 2
    
    let v0_1256_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        (a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a &&& v0) ^^^ (a &&& v1) ^^^ (a) ^^^ (f &&& e) ^^^ (f &&& w) ^^^
        (f &&& v0) ^^^ (f &&& v1) ^^^ (f) ^^^ (e &&& w) ^^^ (e &&& v0) ^^^ (e &&& v1) ^^^ (e) ^^^ (w &&& v0) ^^^
        (w &&& v1) ^^^ (w) ^^^ (v0 &&& v1) ^^^ (v0) ^^^ (v1) // 21 terms, degree 2

    let v0_236_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        (a &&& f) ^^^ (a &&& e) ^^^ (a &&& w) ^^^ (a &&& v0) ^^^ (a &&& v1) ^^^ (f &&& e) ^^^ (f &&& w) ^^^
        (f &&& v0) ^^^ (f &&& v1) ^^^ (e &&& w) ^^^ (e &&& v0) ^^^ (e &&& v1) ^^^ (w &&& v0) ^^^
        (w &&& v1) ^^^ (v0 &&& v1) // 15 terms, degree 2
    
    let v1_34_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        (a &&& f &&& e &&& w) ^^^ (a &&& f &&& e) ^^^ (a &&& f &&& w) ^^^ (a &&& e &&& w) ^^^ (f &&& e &&& w) // 5 terms, degree 4
    
    let v1_4_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        a &&& f &&& e &&& w // 1 term, degree 4
    
    let v1_3456_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        (a &&& f &&& e &&& w) ^^^ (a &&& f &&& e &&& v0) ^^^ (a &&& f &&& e &&& v1) ^^^ (a &&& f &&& e) ^^^
        (a &&& f &&& w &&& v0) ^^^ (a &&& f &&& w &&& v1) ^^^ (a &&& f &&& w) ^^^ (a &&& f &&& v0 &&& v1) ^^^
        (a &&& f &&& v0) ^^^ (a &&& f &&& v1) ^^^ (a &&& e &&& w &&& v0) ^^^ (a &&& e &&& w &&& v1) ^^^
        (a &&& e &&& w) ^^^ (a &&& e &&& v0 &&& v1) ^^^ (a &&& e &&& v0) ^^^ (a &&& e &&& v1) ^^^
        (a &&& w &&& v0 &&& v1) ^^^ (a &&& w &&& v0) ^^^ (a &&& w &&& v1) ^^^ (a &&& v0 &&& v1) ^^^
        (f &&& e &&& w &&& v0) ^^^ (f &&& e &&& w &&& v1) ^^^ (f &&& e &&& w) ^^^ (f &&& e &&& v0 &&& v1) ^^^
        (f &&& e &&& v0) ^^^ (f &&& e &&& v1) ^^^ (f &&& w &&& v0 &&& v1) ^^^ (f &&& w &&& v0) ^^^
        (f &&& w &&& v1) ^^^ (f &&& v0 &&& v1) ^^^ (e &&& w &&& v0 &&& v1) ^^^ (e &&& w &&& v0) ^^^
        (e &&& w &&& v1) ^^^ (e &&& v0 &&& v1) ^^^ (w &&& v0 &&& v1) // 35 terms, degree 4
    
    let v1_456_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        (a &&& f &&& e &&& w) ^^^ (a &&& f &&& e &&& v0) ^^^ (a &&& f &&& e &&& v1) ^^^ (a &&& f &&& w &&& v0) ^^^
        (a &&& f &&& w &&& v1) ^^^ (a &&& f &&& v0 &&& v1) ^^^ (a &&& e &&& w &&& v0) ^^^
        (a &&& e &&& w &&& v1) ^^^ (a &&& e &&& v0 &&& v1) ^^^ (a &&& w &&& v0 &&& v1) ^^^
        (f &&& e &&& w &&& v0) ^^^ (f &&& e &&& w &&& v1) ^^^ (f &&& e &&& v0 &&& v1) ^^^
        (f &&& w &&& v0 &&& v1) ^^^ (e &&& w &&& v0 &&& v1) // 15 terms, degree 4

    let calc_a_value (a_out : Designator) =
        storage.GetOrGenerate (a_out) (fun _ ->
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_overall a_out
            let a,f,e,w,v0,v1 =
                let a,f,e,w = storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
                let v0 = if Option.isSome v0key then storage.Get (Option.get v0key) else repr.Constants.Zero
                let v1 = if Option.isSome v1key then storage.Get (Option.get v1key) else repr.Constants.Zero
                a,f,e,w,v0,v1
            let final =
                let _0 = a ^^^ f
                let _1 = e ^^^ w
                let _2 = v0 ^^^ v1
                let _3 = _0 ^^^ _1
                _2 ^^^ _3
            if Utilities.kbit a_out then final ^^^ repr.Constants.One
            else final
        )

    let calc_f_value (f_out : Designator) =
        storage.GetOrGenerate f_out (fun _ ->
            assert (f_out.Round > 1) // because otherwise, it would be a constant value.
            let bKey, cKey, dKey = Keys.inputKeys_f f_out
            let b, c, d = storage.Get bKey, storage.Get cKey, storage.Get dKey
            let inline isConstant (x : Designator) = x.Round <= 0
            let inline isTrue (x : Designator) = storage.Get x |> repr.IsOne
            if (f_out.Round >= 20 && f_out.Round < 40) || f_out.Round >= 60 then
                b ^^^ c ^^^ d
            elif f_out.Round >= 40 && f_out.Round < 60 then
                // MAJ
                match isConstant bKey, isConstant cKey, isConstant dKey with
                | false, false, false ->
                    (b &&& c) ^^^ (b &&& d) ^^^ (c &&& d)
                | false, false, true ->
                    if isTrue dKey then
                        (b &&& c) ^^^ b ^^^ c
                    else
                        b &&& c
                | false, true, false ->
                    if isTrue cKey then
                        b ^^^ (b &&& d) ^^^ d
                    else
                        b &&& d
                | false, true, true ->
                    match isTrue cKey, isTrue dKey with
                    | false, false -> repr.Constants.Zero
                    | false, true | true, false -> b
                    | true, true -> repr.Constants.One
                | true, false, false ->
                    if isTrue bKey then
                        c ^^^ d ^^^ (c &&& d)
                    else
                        c &&& d
                | true, false, true ->
                    match isTrue bKey, isTrue dKey with
                    | false, false -> repr.Constants.Zero
                    | false, true | true, false -> c
                    | true, true -> repr.Constants.One
                | true, true, false ->
                    match isTrue bKey, isTrue cKey with
                    | false, false -> repr.Constants.Zero
                    | false, true | true, false -> d
                    | true, true -> repr.Constants.One
                | true, true, true ->
                    match isTrue bKey, isTrue cKey, isTrue dKey with
                    | false, true, true | true, false, true | true, true, false | true, true, true -> repr.Constants.One
                    | _ -> repr.Constants.Zero
            else
                // CHOICE
                match isConstant bKey, isConstant cKey, isConstant dKey with
                | false, false, false ->
                    (b &&& c) ^^^ (b &&& d) ^^^ d
                | false, false, true ->
                    if isTrue dKey then
                        repr.Constants.One ^^^ (b &&& c) ^^^ b
                    else
                        b &&& c
                | false, true, false ->
                    if isTrue cKey then
                        (b &&& d) ^^^ b ^^^ d
                    else
                        (b &&& d) ^^^ d
                | false, true, true ->
                    match isTrue cKey, isTrue dKey with
                    | false, false -> repr.Constants.Zero
                    | false, true -> repr.Constants.One ^^^ b
                    | true, false -> b
                    | true, true -> repr.Constants.One
                | true, false, false ->
                    if isTrue bKey then c
                    else d
                | true, false, true ->
                    match isTrue bKey, isTrue dKey with
                    | false, false -> repr.Constants.Zero
                    | false, true -> repr.Constants.One
                    | true, _  -> c
                | true, true, false ->
                    match isTrue bKey, isTrue cKey with
                    | false, _ -> d
                    | true, false -> repr.Constants.Zero
                    | true, true -> repr.Constants.One
                | true, true, true ->
                    match isTrue bKey, isTrue cKey, isTrue dKey with
                    | false, _, false | true, false, _ -> repr.Constants.Zero
                    | false, _, true | true, true, _ -> repr.Constants.One
        )

    let calc_v0_value (v0_out : Designator) =
        storage.GetOrGenerate v0_out (fun _ ->
            let k = Utilities.kbit v0_out                
            match v0_out.Bit, k with
            | 26, _ -> repr.Constants.Zero
            | 25, true -> v0_12_4 v0_out
            | 25, false -> v0_23_4 v0_out
            | _, true -> v0_1256_6 v0_out
            | _, false -> v0_236_6 v0_out
        )
        
    let calc_v1_value (v1_out : Designator) = 
        storage.GetOrGenerate v1_out (fun _ ->
            let k = Utilities.kbit v1_out                
            match v1_out.Bit, k with
            | 26, _ | 25, _ -> repr.Constants.Zero
            | 24, true -> v1_34_4 v1_out
            | 24, false -> v1_4_4 v1_out
            | _, true -> v1_3456_6 v1_out
            | _, false -> v1_456_6 v1_out
        )

    interface ISubCalculator<'T> with
        member __.A k = calc_a_value k
        member __.F k = calc_f_value k
        member __.W k = w.Word k
        member __.V0 k = calc_v0_value k
        member __.V1 k = calc_v1_value k
        member __.Item k = redirect k
