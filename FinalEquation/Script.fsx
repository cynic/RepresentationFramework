// randomly snippets that I've used, mostly for intermediate things.

let getFuncTable6 func =
    seq {
        for v in 0..63 do
            let a = (v &&& 0b100000) <> 0
            let f = (v &&& 0b010000) <> 0
            let e = (v &&& 0b001000) <> 0
            let w = (v &&& 0b000100) <> 0
            let v0 = (v &&& 0b000010) <> 0
            let v1 = (v &&& 0b000001) <> 0
            yield (a,f,e,w,v0,v1), (func a f e w v0 v1)
        }

let getFuncTable5 func =
    seq {
        for v in 0..31 do
            let a = (v &&& 0b10000) <> 0
            let f = (v &&& 0b01000) <> 0
            let e = (v &&& 0b00100) <> 0
            let k = (v &&& 0b00010) <> 0
            let w = (v &&& 0b00001) <> 0
            yield (a,f,e,k,w), (func a f e k w)
        }

let getFuncTable4 func =
    seq {
        for v in 0..15 do
            let a = (v &&& 0b1000) <> 0
            let f = (v &&& 0b0100) <> 0
            let e = (v &&& 0b0010) <> 0
            let w = (v &&& 0b0001) <> 0
            yield (a,f,e,w), (func a f e w)
    }

let getFuncTable3 func =
    seq {
        for v in 0..7 do
            let b = (v &&& 0b100) <> 0
            let c = (v &&& 0b010) <> 0
            let d = (v &&& 0b001) <> 0
            yield (b, c, d), (func b c d)
    }

let printFuncTable6 func =
    printfn "a | f | e | w | v0 | v1 | result"
    let (~%) x = if x then '1' else '0'
    for ((a,f,e,w,v0,v1),result) in getFuncTable6 func do
        printfn "%c | %c | %c | %c |  %c |  %c |    %c" %a %f %e %w %v0 %v1 %result

let printFuncTable5 func =
    printfn "a | f | e | k | w | result"
    let (~%) x = if x then '1' else '0'
    for ((a,f,e,k,w),result) in getFuncTable5 func do
        printfn "%c | %c | %c | %c | %c |    %c" %a %f %e %k %w %result

let printFuncTable4 func =
    printfn "a | f | e | w | result"
    let (~%) x = if x then '1' else '0'
    for ((a,f,e,w),result) in getFuncTable4 func do
        printfn "%c | %c | %c | %c |    %c" %a %f %e %w %result

let printFuncTable3 func =
    printfn "b | c | d | result"
    let (~%) x = if x then '1' else '0'
    for ((b,c,d),result) in getFuncTable3 func do
        printfn "%c | %c | %c |    %c" %b %c %d %result

let (~%) x = not x

let func_1_6 a f e w v0 v1 =
    // 1
    (a && %f && %e && %w && %v0 && %v1) ||
    (%a && f && %e && %w && %v0 && %v1) ||
    (%a && %f && e && %w && %v0 && %v1) ||
    (%a && %f && %e && w && %v0 && %v1) ||
    (%a && %f && %e && %w && v0 && %v1) ||
    (%a && %f && %e && %w && %v0 && v1)

let func_2_6 a f e w v0 v1 =
    // 2
    (a && f && %e && %w && %v0 && %v1) ||
    (a && %f && e && %w && %v0 && %v1) ||
    (a && %f && %e && w && %v0 && %v1) ||
    (a && %f && %e && %w && v0 && %v1) ||
    (a && %f && %e && %w && %v0 && v1) ||
    (%a && f && e && %w && %v0 && %v1) ||
    (%a && f && %e && w && %v0 && %v1) ||
    (%a && f && %e && %w && v0 && %v1) ||
    (%a && f && %e && %w && %v0 && v1) ||
    (%a && %f && e && w && %v0 && %v1) ||
    (%a && %f && e && %w && v0 && %v1) ||
    (%a && %f && e && %w && %v0 && v1) ||
    (%a && %f && %e && w && v0 && %v1) ||
    (%a && %f && %e && w && %v0 && v1) ||
    (%a && %f && %e && %w && v0 && v1)

let func_3_6 a f e w v0 v1 =
    // 3
    (a && f && e && %w && %v0 && %v1) || // afe
    (a && f && %e && w && %v0 && %v1) || // afw
    (a && f && %e && %w && v0 && %v1) || // af0
    (a && f && %e && %w && %v0 && v1) || // af1
    (a && %f && e && w && %v0 && %v1) || // aew
    (a && %f && e && %w && v0 && %v1) || // ae0
    (a && %f && e && %w && %v0 && v1) || // ae1
    (a && %f && %e && w && v0 && %v1) || // aw0
    (a && %f && %e && w && %v0 && v1) || // aw1
    (a && %f && %e && %w && v0 && v1) || // a01
    (%a && f && e && w && %v0 && %v1) || // few
    (%a && f && e && %w && v0 && %v1) || // fe0
    (%a && f && e && %w && %v0 && v1) || // fe1
    (%a && f && %e && w && v0 && %v1) || // fw0
    (%a && f && %e && w && %v0 && v1) || // fw1
    (%a && f && %e && %w && v0 && v1) || // f01
    (%a && %f && e && w && v0 && %v1) || // ew0
    (%a && %f && e && w && %v0 && v1) || // ew1
    (%a && %f && e && %w && v0 && v1) || // e01
    (%a && %f && %e && w && v0 && v1)    // w01

let func_4_6 a f e w v0 v1 =
    // 4
    (%a && %f && e && w && v0 && v1) ||
    (%a && f && %e && w && v0 && v1) ||
    (%a && f && e && %w && v0 && v1) ||
    (%a && f && e && w && %v0 && v1) ||
    (%a && f && e && w && v0 && %v1) ||
    (a && %f && %e && w && v0 && v1) ||
    (a && %f && e && %w && v0 && v1) ||
    (a && %f && e && w && %v0 && v1) ||
    (a && %f && e && w && v0 && %v1) ||
    (a && f && %e && %w && v0 && v1) ||
    (a && f && %e && w && %v0 && v1) ||
    (a && f && %e && w && v0 && %v1) ||
    (a && f && e && %w && %v0 && v1) ||
    (a && f && e && %w && v0 && %v1) ||
    (a && f && e && w && %v0 && %v1)

let func_5_6 a f e w v0 v1 =
    // 5
    (%a && f && e && w && v0 && v1) ||
    (a && %f && e && w && v0 && v1) ||
    (a && f && %e && w && v0 && v1) ||
    (a && f && e && %w && v0 && v1) ||
    (a && f && e && w && %v0 && v1) ||
    (a && f && e && w && v0 && %v1)

let func_6_6 a f e w v0 v1 =
    // 6
    a && f && e && w && v0 && v1

let func_1_4 a f e w =
    // 1
    (a && %f && %e && %w) ||
    (%a && f && %e && %w) ||
    (%a && %f && e && %w) ||
    (%a && %f && %e && w)

let func_2_4 a f e w =
    // 2
    (a && f && %e && %w) ||
    (a && %f && e && %w) ||
    (a && %f && %e && w) ||
    (%a && f && e && %w) ||
    (%a && f && %e && w) ||
    (%a && %f && e && w)

let func_3_4 a f e w =
    // 3
    (%a && f && e && w) ||
    (a && %f && e && w) ||
    (a && f && %e && w) ||
    (a && f && e && %w)

let func_4_4 a f e w =
    // 4
    (a && f && e && w)

let func_1256_6 a f e w v0 v1 =
    func_1_6 a f e w v0 v1 ||
    func_2_6 a f e w v0 v1 ||
    func_5_6 a f e w v0 v1 ||
    func_6_6 a f e w v0 v1

let func_236_6 a f e w v0 v1 =
    func_2_6 a f e w v0 v1 ||
    func_3_6 a f e w v0 v1 ||
    func_6_6 a f e w v0 v1

let func_3456_6 a f e w v0 v1 =
    func_3_6 a f e w v0 v1 ||
    func_4_6 a f e w v0 v1 ||
    func_5_6 a f e w v0 v1 ||
    func_6_6 a f e w v0 v1

let func_456_6 a f e w v0 v1 =
    func_4_6 a f e w v0 v1 ||
    func_5_6 a f e w v0 v1 ||
    func_6_6 a f e w v0 v1

let func_12_4 a f e w =
    func_1_4 a f e w ||
    func_2_4 a f e w

let func_23_4 a f e w =
    func_2_4 a f e w ||
    func_3_4 a f e w

let func_34_4 a f e w =
    func_3_4 a f e w ||
    func_4_4 a f e w

let func_sum_5 a f e k w =
    let (~%) x = if x then 1 else 0
    %a + %f + %e + %k + %w &&& 0b001 > 0
    
let func_carry0_5 a f e k w =
    let (~%) x = if x then 1 else 0
    %a + %f + %e + %k + %w &&& 0b010 > 0

let func_carry1_5 a f e k w =
    let (~%) x = if x then 1 else 0
    %a + %f + %e + %k + %w &&& 0b100 > 0

let func_choice b c d =
    (b && c) || (not b && d)

let func_majority b c d =
    (b && c) || (b && d) || (c && d)

let func_parity b c d =
    b <> c <> d

// then:
// getFuncTableN WHATEVER_FUNC_HERE |> Seq.map (snd >> (fun x -> if x then 1 else 0) >> string) |> String.concat ",";;

(* // now, via SAGE:

sage: from sage.crypto.boolean_function import BooleanFunction
sage: B_1256_6 = BooleanFunction([0,1,1,1,1,1,1,0,1,1,1,0,1,0,0,0,1,1,1,0,1,0,0,0,1,0,0,0,0,0,0,1,1,1,1,0,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,1,1,1])
sage: B_236_6 = BooleanFunction([0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,0,0,1,1,1,1,1,1,0,1,1,1,0,1,0,0,0,0,1,1,1,1,1,1,0,1,1,1,0,1,0,0,0,1,1,1,0,1,0,0,0,1,0,0,0,0,0,0,1])
sage: B_3456_6 = BooleanFunction([0,0,0,0,0,0,0,1,0,0,0,1,0,1,1,1,0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,1,0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
sage: B_456_6 = BooleanFunction([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,1,1,1,0,0,0,0,0,0,0,1,0,0,0,1,0,1,1,1,0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,1])
sage: B_12_4 = BooleanFunction([0,1,1,1,1,1,1,0,1,1,1,0,1,0,0,0])
sage: B_23_4 = BooleanFunction([0,0,0,1,0,1,1,1,0,1,1,1,1,1,1,0])
sage: B_34_4 = BooleanFunction([0,0,0,0,0,0,0,1,0,0,0,1,0,1,1,1])
sage: B_4_4 = BooleanFunction([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1])
sage: B_1256_6.algebraic_normal_form()
x0*x1 + x0*x2 + x0*x3 + x0*x4 + x0*x5 + x0 + x1*x2 + x1*x3 + x1*x4 + x1*x5 + x1 + x2*x3 + x2*x4 + x2*x5 + x2 + x3*x4 + x3*x5 + x3 + x4*x5 + x4 + x5
sage: B_236_6.algebraic_normal_form()
x0*x1 + x0*x2 + x0*x3 + x0*x4 + x0*x5 + x1*x2 + x1*x3 + x1*x4 + x1*x5 + x2*x3 + x2*x4 + x2*x5 + x3*x4 + x3*x5 + x4*x5
sage: B_3456_6.algebraic_normal_form()
x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x2*x5 + x0*x1*x2 + x0*x1*x3*x4 + x0*x1*x3*x5 + x0*x1*x3 + x0*x1*x4*x5 + x0*x1*x4 + x0*x1*x5 + x0*x2*x3*x4 + x0*x2*x3*x5 + x0*x2*x3 + x0*x2*x4*x5 + x0*x2*x4 + x0*x2*x5 + x0*x3*x4*x5 + x0*x3*x4 + x0*x3*x5 + x0*x4*x5 + x1*x2*x3*x4 + x1*x2*x3*x5 + x1*x2*x3 + x1*x2*x4*x5 + x1*x2*x4 + x1*x2*x5 + x1*x3*x4*x5 + x1*x3*x4 + x1*x3*x5 + x1*x4*x5 + x2*x3*x4*x5 + x2*x3*x4 + x2*x3*x5 + x2*x4*x5 + x3*x4*x5
sage: B_456_6.algebraic_normal_form()
x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x2*x5 + x0*x1*x3*x4 + x0*x1*x3*x5 + x0*x1*x4*x5 + x0*x2*x3*x4 + x0*x2*x3*x5 + x0*x2*x4*x5 + x0*x3*x4*x5 + x1*x2*x3*x4 + x1*x2*x3*x5 + x1*x2*x4*x5 + x1*x3*x4*x5 + x2*x3*x4*x5
sage: B_12_4.algebraic_normal_form()
x0*x1 + x0*x2 + x0*x3 + x0 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3
sage: B_23_4.algebraic_normal_form()
x0*x1 + x0*x2 + x0*x3 + x1*x2 + x1*x3 + x2*x3
sage: B_34_4.algebraic_normal_form()
x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3
sage: B_4_4.algebraic_normal_form()
x0*x1*x2*x3
*)
