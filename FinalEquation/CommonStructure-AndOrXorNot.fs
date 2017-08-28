namespace FinalEquation.CommonStructure.SubCalculations

open FinalEquation.CommonStructure

type AndOrXorNot<'T>(dwlen : uint32, w : IWords<'T>, recurse, repr : IRepresentation<'T>, storage : IStorage<'T>) as __ =
    do
        Internal.init_subcalc_constants storage repr

    let redirect = Internal.redirect __ storage

    let storage =
        match recurse with
        | Always -> Internal.alwaysRecurse storage redirect
        | Never -> Internal.neverRecurse storage
        | Depends f -> Internal.sometimesRecurse storage w dwlen redirect f
            
    let (~%) x = repr.Not x
    let (&&&) a b = repr.And a b
    let (|||) a b = repr.Or a b
    let (^^^) a b = repr.Xor a b

    let v0_12_4 (t : Designator) : 'T = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        
        let a', f', e', w' = %a, %f, %e, %w
        let _0 = f &&& w'
        let _1 = e' &&& w
        let _2 = e &&& f'
        let _3 = e' &&& f'
        let _4 = f' ||| e'
        let _5 = _0 ||| _1
        let _6 = _5 ||| _2
        let _7 = w' &&& _4
        let _8 = _7 ||| _3
        let _9 = _6 &&& a'
        let _a = _8 &&& a
        let out = _a ||| _9
        out
    
    let v0_23_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        
        let a', f', e', w' = %a, %f, %e, %w
        let _0 = a &&& w'
        let _1 = e' &&& w
        let _2 = a' &&& e
        let _3 = e ||| a
        let _4 = a &&& e
        let _5 = _0 ||| _1
        let _6 = _5 ||| _2
        let _7 = w &&& _3
        let _8 = _7 ||| _4
        let _9 = f &&& _6
        let _a = f' &&& _8
        let out = _9 ||| _a
        out
    
    let v0_1256_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        
        let a', f', e', w', v0', v1' = %a, %f, %e, %w, %v0, %v1
        let _0 = a &&& f
        let _1 = a' &&& f'
        let _2 = w' ||| v0'
        let _3 = a' ||| v0'
        let _4 = a' &&& v0
        let _5 = a' &&& v0'
        let _6 = v1 &&& w
        let _7 = v1 &&& w'
        let _8 = v1' &&& w'
        let _9 = a' &&& f
        let _a = a &&& f'
        let _b = _9 ||| _a
        let _c = _0 &&& _6
        let _d = _1 &&& _7
        let _e = _1 &&& _8
        let _f = _1 &&& w
        let _g = _b &&& w'
        let _h = a &&& _2
        let _i = w &&& %_1
        let _j = w' &&& %_0
        let _k = w' &&& _3
        let _l = w' &&& _1
        let _m = w &&& _0
        let _n = _c &&& v0
        let _o = _f ||| _g
        let _p = _h ||| _4
        let _q = _k ||| _5
        let _r = _i ||| _0
        let _s = _j ||| _1
        let _t = v0' &&& _o
        let _u = f' &&& _p
        let _v = f &&& _q
        let _w = v1 &&& _r
        let _x = v1' &&& _s
        let _y = _d ||| _t
        let _z = _u ||| _v
        let _A = _m ||| _w
        let _B = _e ||| _c
        let _C = _l ||| _x
        let _D = v1' &&& _z
        let _E = _y ||| _D
        let _F = v0 &&& _A
        let _G = v0' &&& _C
        let _H = _B ||| _F
        let _I = _H ||| _G
        let _J = e' &&& _E
        let _K = _n ||| _J
        let _L = e &&& _I
        let out = _K ||| _L
        out
    
    let v0_236_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v0 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        
        let a', f', e', w', v0', v1' = %a, %f, %e, %w, %v0, %v1
        let _0 = v0' &&& e'
        let _1 = v0 &&& e
        let _2 = v1 &&& w
        let _3 = a &&& v1'
        let _4 = a' &&& v1
        let _5 = e &&& v0'
        let _6 = e' &&& w
        let _7 = v0 &&& w'
        let _8 = v0 &&& v1'
        let _9 = v0' &&& v1
        let _a = v1' &&& w
        let _b = a' &&& w
        let _c = v0' ||| a'
        let _d = a &&& _0
        let _e = a' &&& _0
        let _f = _e &&& _2
        let _g = a &&& _1
        let _h = _g &&& _2
        let _i = _3 ||| _4
        let _j = _7 ||| _6
        let _k = _j ||| _5
        let _l = v0 &&& _4
        let _m = _7 ||| _a
        let _n = _m ||| _9
        let _o = _b &&& _8
        let _p = _b ||| _3
        let _q = v1 &&& _c
        let _r = _q ||| _8
        let _s = _i &&& %_1
        let _t = _d ||| _s
        let _u = a' &&& _k
        let _v = _d ||| _u
        let _w = a &&& _n
        let _x = _l ||| _w
        let _y = v0' &&& _p
        let _z = w' &&& _r
        let _A = v1' &&& _v
        let _B = w' &&& _t
        let _C = _y ||| _z
        let _D = e &&& _C
        let _E = e' &&& _x
        let _F = _h ||| _B
        let _G = _F ||| _A
        let _H = _o ||| _E
        let _I = _H ||| _D
        let _J = f &&& _G
        let _K = f' &&& _I
        let _L = _J ||| _K
        let out = _f ||| _L
        out
    
    let v1_34_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        
        let _0 = a &&& e
        let _1 = e ||| a
        let _2 = _0 &&& w
        let _3 = w &&& _1
        let _4 = _3 ||| _0
        let _5 = f &&& _4
        let out = _2 ||| _5
        out
    
    let v1_4_4 (t : Designator) = 
        let a, f, e, w = 
            let akey, fkey, ekey, wkey, _, _ = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey
        
        let _0 = a &&& f
        let _1 = e &&& w
        let out = _0 &&& _1
        out
    
    let v1_3456_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        
        let _0 = a &&& e
        let _1 = a ||| e
        let _2 = v0 ||| f
        let _3 = _0 &&& w
        let _4 = w &&& _1
        let _5 = f &&& _1
        let _6 = f ||| _1
        let _7 = _2 ||| _1
        let _8 = _4 ||| _0
        let _9 = _5 ||| _0
        let _a = w &&& _6
        let _b = _5 ||| _0
        let _c = v0 &&& _6
        let _d = w &&& _7
        let _e = f &&& _8
        let _f = _9 ||| _a
        let _g = v0 &&& _f
        let _h = _b ||| _c
        let _i = _h ||| _d
        let _j = _3 ||| _e
        let _k = _j ||| _g
        let _l = v1 &&& _i
        let out = _k ||| _l
        out
    
    let v1_456_6 (t : Designator) = 
        let a, f, e, w, v0, v1 = 
            let akey, fkey, ekey, wkey, v0key, v1key = Keys.inputKeys_v1 t
            storage.Get akey, storage.Get fkey, storage.Get ekey, storage.Get wkey, storage.Get (Option.get v0key), storage.Get (Option.get v1key)
        
        let _0 = a &&& e
        let _1 = e ||| a
        let _2 = v1 &&& w
        let _3 = _0 &&& _2
        let _4 = _0 &&& w
        let _5 = _1 &&& w
        let _6 = f &&& _1
        let _7 = f ||| _1
        let _8 = _5 ||| _0
        let _9 = _6 ||| _0
        let _a = w &&& _7
        let _b = v1 &&& _8
        let _c = _4 ||| _b
        let _d = _9 ||| _a
        let _e = v1 &&& _d
        let _f = f &&& _8
        let _g = _4 ||| _f
        let _h = f &&& _c
        let _i = _3 ||| _h
        let _j = _g ||| _e
        let _k = v0 &&& _j
        let out = _i ||| _k
        out

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
            if Utilities.kbit a_out then %final
            else final
        )
        
    let calc_f_value (f_out : Designator) =
        storage.GetOrGenerate f_out (fun _ ->
            let b, c, d = 
                let bkey, ckey, dkey = Keys.inputKeys_f f_out
                storage.Get bkey, storage.Get ckey, storage.Get dkey
            
            if f_out.Round < 20 then // CHOICE
                let _0 = %b &&& d
                let _1 = b &&& c
                _0 ||| _1
            elif f_out.Round < 40 || f_out.Round >= 60 then // PARITY
                let _0 = b ^^^ c
                _0 ^^^ d
            else // MAJORITY
                let _0 = b &&& c
                let _1 = b &&& d
                let _2 = c &&& d
                let _3 = _0 ||| _1
                _2 ||| _3
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
