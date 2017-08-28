module FinalEquation.AIG.Bobbling

type Subtree =
/// This is a Primary Input or a cutoff point.
| T of uint32
/// L = Level.
| L of ident : uint32 * left : Subtree * right : Subtree

type SubtreeDiff =
/// Input/Output point
| IO of uint32
/// Inverter
| Inv of SubtreeDiff
/// Sub = Subtree
| Sub of left : SubtreeDiff * right : SubtreeDiff
| Const of bool

let rewriteCache = System.Collections.Generic.Dictionary() // I want a structure ordered by truth-table string.

// Idea:
// Make a cut that has the desired variable near the "bottom".
// Factor out the desired variable s.t. Boolean expansion results in T & F branches.
// Use Karnaugh maps / Quine-McCluskey for exact minimization of each branch.
// Join the two sides using OR(x,y) = NOT(AND(NOT(x),NOT(y))), incorporating desired variable at the end.

/// convert doubled value to idx value
let idxOf (dwlen : uint32) (x : uint32) : int = (x >>> 1) - dwlen - 1u |> int
/// convert idx value to (positive) doubled value
let positiveNodeOf dwlen x = (dwlen <<< 1) + 2u + (uint32 x <<< 1)

//let counters = Array.zeroCreate 60
let tracker = System.Collections.Generic.Dictionary()
let track (ln : string) =
    if tracker.ContainsKey ln then tracker.[ln] <- tracker.[ln] + 1
    else tracker.[ln] <- 1

/// this is a cache of binary vectors of different lengths, up to 2^8
let vectorCache =
    let basic : uint32[] = Array.init 256 uint32
    let cache = Array.init 9 (fun i -> Array.sub basic 0 (int (2.**float i)))
    fun numInputs -> cache.[numInputs]

let stringVectorCache =
    let cache =
        Array.init 9 (fun n ->
            vectorCache n |> Array.map (fun i -> System.Convert.ToString(int i, 2).PadLeft(n, '0'))
        )
    fun numInputs -> cache.[numInputs]

let evaluate_cut vars cut = // returns the output vectors
    let leftmost = 1u <<< (Array.length vars - 1)
    let rec evaluate cut vector =
        match cut with
        | L(_, (L(xNode, _, _) as x), (L(yNode, _, _) as y))
        | L(_, (T xNode as x), (T yNode as y))
        | L(_, (L(xNode, _, _) as x), (T yNode as y))
        | L(_, (T xNode as x), (L(yNode, _, _) as y)) ->
            // these next calculations XOR the input-vector bit with the "polarity" of the value
            let x' = if xNode=1u then true elif xNode=0u then false else (evaluate x vector) <> (xNode%2u=1u)
            let y' = if yNode=1u then true elif yNode=0u then false else (evaluate y vector) <> (yNode%2u=1u)
            let result = x' && y'
            result
        | T 0u -> false
        | T 1u -> true
        | T v ->
            // find idx of the correct variable.
            let idx = Array.findIndex (fun x -> v>>>1 = x) vars
            // use this idx to index the input vector.
            let mask = leftmost >>> idx
            // polarity calc taken care of at higher level.
            let result = vector &&& mask > 0u
            result
    let input_vectors = vectorCache (Array.length vars)
    Array.init input_vectors.Length (fun i -> evaluate cut input_vectors.[i])

let evaluate_subtree vars cut = // returns the output vectors
    let leftmost = 1u <<< (Array.length vars - 1)
    let rec evaluate cut vector =
        match cut with
        | IO v ->
            // find idx of the correct variable.
            let idx = Array.findIndex (fun x -> v >>>1 = x) vars
            // use this idx to index the input vector.
            let mask = leftmost >>> idx
            // polarity calc taken care of at higher level.
            vector &&& mask > 0u
        | Inv x -> not (evaluate x vector)
        | Sub(a, b) ->
            (evaluate a vector) && (evaluate b vector)
        | Const v -> v
    let input_vectors = vectorCache (Array.length vars)
    Array.init input_vectors.Length (fun i -> evaluate cut input_vectors.[i])

module ``Quine-McCluskey`` =
    module SimpleDNF = // a lot of this is taken from LogicOnlyDNF & simplified.
        // The idea is that it is *just* enough to help with the distribution of terms during Petrick's method.
        type DNF =
        | Positive of int
        /// an OR of ANDs
        | Terms of Set<Set<DNF>>
        with
            override __.ToString () =
                let sb = System.Text.StringBuilder()
                let rec stringify x =
                    match x with
                    | Positive x -> sb.AppendFormat("@{0}", x) |> ignore
                    | Terms ands ->
                        for andClause in ands do
                            sb.Append "(" |> ignore
                            for andTerm in andClause do
                                stringify andTerm
                                sb.Append " ∧ " |> ignore
                            if sb.Length-3 >= 0 then sb.Remove(sb.Length-3, 3).Append(") ∨ ") |> ignore
                        if sb.Length-3 >= 0 then sb.Remove(sb.Length-3, 3) |> ignore
                stringify __
                sb.ToString()

        /// Apply absorption laws (a ∨ (a ∧ b) = a) and (¬a ∨ (a ∧ b) = (¬a ∨ b)) to /xs/
        let absorption xs =
            let maxCount = xs |> Seq.map Set.count |> Seq.max
            let absorb state item =
                if Set.count item = maxCount then
                    state
                else
                    // positive absorption
                    state |> Set.filter (not << Set.isProperSubset item)
            let rec continueAbsorption state =
                let result = Set.fold absorb state state
                if result = state then
                    result
                else
                    continueAbsorption result
            continueAbsorption xs

        let rec _and dnfA dnfB =
            match dnfA, dnfB with
            | Positive x, Positive y when x = y -> Positive x
            | Positive x, Positive y -> Terms (set [ set [Positive x; Positive y] ])
            | Positive _, Terms _ -> _and (Terms (set [ set [dnfA] ])) dnfB
            | Terms _, Positive _ -> _and dnfA (Terms (set [ set [dnfB] ]))
            | Terms andsA, Terms andsB ->
                let rec add = function
                | [] -> Seq.empty
                | x::xs ->
                    seq {
                        for b in andsB do yield Set.union x b
                        yield! add xs
                    }
                let result = add (Set.toList andsA) |> set
                if Set.count result = 1 && Set.count (Seq.head result) = 1 then
                    Seq.head (Seq.head result)
                else
                    Terms (result)

        let rec _or dnfA dnfB =
            match dnfA, dnfB with
            | Positive _, Positive _ -> _or (Terms (set [set [dnfA] ])) (Terms (set [set [dnfB] ]))
            | Terms _, Positive _ -> _or dnfA (Terms (set [set [dnfB] ]))
            | Positive _, Terms _ -> _or (Terms (set [set [dnfA] ])) dnfB
            | Terms andsA, Terms andsB when andsA = andsB ->
                if Set.count andsA = 1 && Set.count (Seq.head andsA) = 1 then
                    Seq.head (Seq.head andsA)
                else
                    dnfA
        (*
           andsA and andsB are both in DNF form.  So what I really need to do is figure out how
           andsA affects terms in andsB (or vice-versa, of course).  Application of a term can
           result in ...

          - absorption
             - positive: a ∨ (a ∧ b) = b
          - retention a ∨ (b ∨ c) = a ∨ b ∨ c

          Since andsA and andsB are both in DNF form, I only need to check each term of andsA
          against the andsB set (or vice-versa).
        *)
            | Terms andsA, Terms andsB ->
                let result = Set.union andsA andsB
                let result = absorption result
                if Set.count result = 1 && Set.count (Seq.head result) = 1 then
                    Seq.head (Seq.head result)
                else
                    Terms result

    open SimpleDNF

    /// returns true-input rows with associated minterm lists
    let true_inputs_for ttable =
        let numInputs = System.Math.Log(Array.length ttable |> float, 2.) |> int
        let string_input_vectors = stringVectorCache numInputs
        ttable
        |> Array.mapi (fun i result -> string_input_vectors.[i], i, result)
        |> Array.choose (fun (vec, row, result) -> if result then Some (vec,[row]) else None)

    let stringHammingWeight = Seq.filter ((=) '1') >> Seq.length

    let combine = // combining function that combines two strings
        let sb = System.Text.StringBuilder ()
        // go through the two, and if they differ by only one place, they can be combined.
        fun (x : string) (y : string) ->
            ignore <| sb.Clear ()
            let _, diffcount =
                Seq.fold2 (fun (result : System.Text.StringBuilder,count) (i : char) j ->
                    if i = j then result.Append(i), count
                    else result.Append('-'),(count+1)
                ) (sb,0) x y
            if diffcount <= 1 then Some(sb.ToString()) else None

    // combine adjacent groups (where Hamming weight differs by 1).
    let rec combineAdjacent groups =
        let combinedFlags =
            Array.init (Array.length groups) (fun i -> groups.[i] |> snd |> Array.length |> Array.zeroCreate)
        let mutable something_combined = false
        let combinedResults = System.Collections.Generic.List()
        for groupIdx = 1 to Array.length groups - 1 do
            let hwt0, vec0 = groups.[groupIdx-1]
            let hwt1, vec1 = groups.[groupIdx]
            if hwt1-hwt0 = 1 then // this is OK - can combine these groups.
                for v0Idx = 0 to Array.length vec0 - 1 do
                    let v0, mt0 = vec0.[v0Idx]
                    for v1Idx = 0 to Array.length vec1 - 1 do
                        let v1, mt1 = vec1.[v1Idx]
                        match combine v0 v1 with
                        | Some combined ->
                            something_combined <- true
                            combinedFlags.[groupIdx-1].[v0Idx] <- true
                            combinedFlags.[groupIdx].[v1Idx] <- true
                            combinedResults.Add(combined, mt0 @ mt1)
                        | None -> ()
        if not something_combined then // no more combination possible - stop here!
            // I don't need to split it by Hamming weight now.
            // I just need the strings & minterms.
            groups
            |> Seq.map snd
            |> Seq.collect (fun v_and_mt -> v_and_mt |> Seq.map (fun (v,mt) -> v, Set.ofList mt))
            |> Seq.distinctBy fst
            |> Seq.toArray
        else
            // now go through the list of groups and add in those results that could not be combined.
            for groupIdx = 0 to Array.length combinedFlags - 1 do
                for i = 0 to Array.length combinedFlags.[groupIdx] - 1 do
                    if combinedFlags.[groupIdx].[i] = false then
                        let _, vec = groups.[groupIdx]
                        combinedResults.Add vec.[i]
            // now make another list of things, again ordered by Hamming weight.
            let newGroup =
                combinedResults
                |> Seq.distinctBy fst
                |> Seq.toArray
                |> Array.groupBy (fun (vec,_) -> stringHammingWeight vec)
            combineAdjacent newGroup

    let petricks_method (minterms : System.Collections.Generic.HashSet<_>) implicants_and_minterms =
        // Step 4: separate the implicants into 'essential' and 'non-essential, but prime' implicants.
        // This will reduce the "columns" (of minterms) and the "rows" (of implicants).
        // Any implicant that is the ONLY cover of a minterm is an 'essential' implicant.
        let essentials = System.Collections.Generic.HashSet()
        // the minterms which are covered by the essentials
        let covered_minterms = System.Collections.Generic.List()
        let find_essential minterm implicants_and_minterms =
            let rec find_implicants implicant idx =
                if idx = Array.length implicants_and_minterms then
                    if Option.isNone implicant then failwithf "Error - no implicant covers minterm %d" minterm
                    else implicant
                else
                    let vec, minterms = implicants_and_minterms.[idx]
                    // check if this vector covers the minterm
                    match Set.contains minterm minterms, implicant with
                    | true, Some _ -> None // can't be essential if more than one covers the minterm.
                    | true, None -> find_implicants (Some (vec, minterms)) (idx+1)
                    | false, _ -> find_implicants implicant (idx+1)
            find_implicants None 0
        for minterm in minterms do
            find_essential minterm implicants_and_minterms
            |> Option.iter (fun (vec,mt) ->
                essentials.Add vec |> ignore
                covered_minterms.AddRange mt
            )
        // now, everything NOT in essentials is going to be a non-essential prime implicant.
        let best_remaining =
            let remaining =
                let covered_minterms = Set.ofSeq covered_minterms
                implicants_and_minterms
                |> Array.choose (fun (vec, mt) ->
                    if essentials.Contains vec then None
                    else
                        Some (vec, Set.difference mt covered_minterms)
                )
            // now.  If I arrange the minterms in columns, and the vectors in rows, I get a table.
            // The intersection of vectors with minterms is marked with an X in this table.
            // Each row is labeled, in my case, I'll choose the vector-string as the label.
            // Then Wikipedia sayeth:
            //   "build a product of sums of the rows where each row is added, and columns are multiplied together"
            // Let's start by MUTATING the minterms to remove the essentials.
            minterms.ExceptWith(covered_minterms)
            let make_term minterm remaining =
                // I know for a fact that this will cover more than 1 minterm ...
                // If it doesn't, then something's gone wrong with the previous step
                // of finding 'essential' prime implicants
                remaining
                |> Array.indexed
                |> Array.choose (fun (i,(_,mt)) ->
                    if Set.contains minterm mt then Some (SimpleDNF.Positive i)
                    else None
                ) |> Array.reduce _or
            match minterms.Count with
            | 0 -> [||] // there are no items remaining - we're done!
            | _ ->
                match remaining with
                | [|(vec,_)|] -> [|vec|] // only one remaining? Easy.
                | _ -> // ok, need to use Petrick's method for this... :-/
                    // returns a BitArray with indices that indicate the terms separated by +.
                    let reduced =
                        match minterms.Count with
                        | 1 -> make_term (Seq.head minterms) remaining
                        | _ ->
                            Seq.map (fun minterm -> make_term minterm remaining) minterms
                            |> Seq.reduce _and
                    // now, I can take any one of these.  I should take the shortest & expand it.
                    let shortest =
                        match reduced with
                        | Positive i -> [|fst remaining.[i]|]
                        | Terms terms ->
                            let vars = terms |> Seq.sortBy (fun x -> Set.count x) |> Seq.head
                            Set.toArray vars
                            |> Array.map (function Positive i -> fst remaining.[i] | _ -> failwith "DNF error - term shouldn't consist of terms")
                    shortest
        let final = Seq.append essentials best_remaining |> Seq.toArray
        final

    let quine_mccluskey ttable = // the /variables/ are undoubled.
        // Step 1: choose only the 1-valued input vectors (in string form).
        let true_inputs = true_inputs_for ttable
        let minterms =
            System.Collections.Generic.HashSet(
                ttable |> Seq.indexed |> Seq.choose (fun (i,v) -> if v then Some i else None)
            )
        // Step 2: group them by Hamming weight.
        let grouped = true_inputs |> Array.groupBy (fun (vec,_) -> stringHammingWeight vec)
        Array.sortInPlace grouped
        // Step 3: combine adjacent groups (where Hamming weight differs by 1).
        let implicants_and_minterms = combineAdjacent grouped
        // Step 4: use Petrick's Method to get down to a minimum.
        let minimum_remaining = petricks_method minterms implicants_and_minterms
        // and return the resulting strings.
        minimum_remaining

let mapBranchStrings (variables :_[]) strings = // all of these must be ORed together
    let mapString s = // all of these must be ANDed together.
        let basicVars =
            s |> Seq.mapi (fun i v -> i+1, v) // i+1 because we exclude the leftmost of the vars, and include it last.
            |> Seq.choose (fun (i,ch) ->
                match ch with
                | '0' -> Some ( Inv ( IO (variables.[i] <<< 1) ) )
                | '1' -> Some ( IO ( variables.[i] <<< 1 ) )
                | '-' -> None
                | _ -> failwithf "Unexpected character in string-mapping (%c)" ch
            ) |> Seq.toList
        match basicVars with
        | [] -> failwith "Something weird has happened.  Empty clause?"
        | [x] -> x
        | _ ->
            basicVars |> List.reduce (fun state item -> Sub(state, item))
    // check: if /strings/ is a single item consisting of don't-care symbols, then
    // the result from here is a Constant True - because no matter what, the output
    // will be true.  Remember: QM works by isolating the true rows!
    if Array.length strings = 1 && strings.[0] |> Seq.forall ((=) '-') then
        Const true
    else
        // let's do a real mapping.
        match strings |> Array.map mapString with
        | [||] -> failwith "Impossible - empty DNF?"
        | [|x|] -> x
        | xs -> xs |> Array.reduce (fun state item -> Inv(Sub(Inv state, Inv item)) )

let bubbleOut dwlen undoubled (aag : AAG) =
    let idxOf = idxOf dwlen
    let positiveNodeOf = positiveNodeOf dwlen
    let abc = ABCInterface(dwlen)
    let modified = System.Collections.Generic.List(aag.Ands.Length * 2)
    modified.AddRange aag.Ands

    let ands_start = (dwlen <<< 1) + 2u // this is the positive node value of the very first 'and'

    let evaluate_aag (aag : AAG) = 
        let leftmost = 1u <<< (int dwlen - 1)
        let eval (vector : uint32) =
            let bs = System.Collections.Generic.Dictionary()
            bs.[0u] <- false
            bs.[1u] <- true
            for i = 1 to int dwlen do
                let doubled = uint32 (i <<< 1)
                bs.[doubled] <- vector &&& (leftmost >>> (i-1)) > 0u
                bs.[doubled + 1u] <- not bs.[doubled]
            let rec calculate (node : uint32) =
                if not (bs.ContainsKey node) then
                    let a, b = aag.Ands.[idxOf node]
                    let aV, bV = calculate a, calculate b
                    let result = aV && bV
                    let positive = node &&& 0xfffffffeu
                    bs.[positive] <- result
                    bs.[positive ^^^ 1u] <- not result
                bs.[node]
            calculate aag.Output
        let inputVectors = vectorCache (int dwlen)
        inputVectors |> Array.map (fun vec -> eval vec)

    let make_cut node_idx = // /upnode/ is the node to start with.
        // start with a positive root so that later interpretation doesn't
        // mess with polarity.
        let upnode = positiveNodeOf node_idx
        let rec nodesOf node level =
            if node < ands_start then
                T node
            else
                let a,b = modified.[idxOf node]
                if level = 3 then L(node, T a, T b)
                else
                    L (node, nodesOf a (level+1), nodesOf b (level+1))
        let cut = nodesOf upnode 1
        let rec check node level =
            match node, level >= 3 with
            | T _, false -> false
            | T v, true -> v>>>1=undoubled
            | L(_, a, b), _ -> check a (level+1) || check b (level+1)
        if check cut 0 then Some cut else None

    let inverted = System.Collections.Generic.List (Array.zeroCreate aag.Ands.Length)

    // at the end of the day, I should have a patched /modified/ list.
    // IF the root is inverted, then the index in the /inverted/ list must be set to true.
    // If completely NEW nodes are created, they are added to /modified/ and a new node is added to /inverted/.
    // The *main* change is that /modified/ should be reassigned.
    let patch (root, diff) =
        // I'm going to be very lazy and simple here.
        // Make new nodes for everything, and rely on strashing.
        let makeNode a b =
            modified.Add ((a, b))
            inverted.Add false
            let v = positiveNodeOf (modified.Count - 1)
            v
        let rootIdx = idxOf root
        let rec patch diff depth =
            match diff, depth with
            | Inv x, 0 ->
                inverted.[rootIdx] <- true
                patch x depth
            | Inv x, _ -> patch x (depth+1) ^^^ 1u
            | Sub (a,b), 0 ->
                modified.[rootIdx] <- (patch a (depth+1), patch b (depth+1))
                root
            | Sub (a,b), _ ->
                makeNode (patch a (depth+1)) (patch b (depth+1))
            | IO x, 0 -> modified.[rootIdx] <- (x, 0u); root
            | IO x, _ -> x
            | Const false, 0 -> modified.[rootIdx] <- (0u, 0u); root
            | Const false, _ -> 0u
            | Const true, 0 -> modified.[rootIdx] <- (1u, 1u); root
            | Const true, _ -> 1u
        let result = patch diff 0 |> ignore
        result

    let rec rewrite idx =
        // create a suitable 7-cut, and rewrite it as necessary.
        match make_cut idx with
        | None -> ()
        | Some cut ->
            // make a truth table.  The desired variable should be the "leftmost" entry.
            let variables =
                let inputs = System.Collections.Generic.HashSet()
                let rec getVars node =
                    match node with
                    | T x ->
                        if x > 1u then // ignore true/false constants; they aren't variables.
                            ignore <| inputs.Add (x >>> 1)
                    | L(_, a, b) -> getVars a; getVars b
                getVars cut // needed to populate /inputs/
                if not <| inputs.Remove undoubled then failwith "Logic error (probably in make_cut)"
                Array.ofList (undoubled::List.ofSeq inputs)

            // to make a truth table, I need to evaluate this cut.
            let truth_table = evaluate_cut variables cut
            let diff =
                // take care of the very simple case: all-false, all-true, and one-variable
                if truth_table |> Array.forall ((=) true) then
                    Const true
                elif truth_table |> Array.forall ((=) false) then
                    Const false
                elif truth_table = [|false;true|] then
                    IO (undoubled <<< 1)
                elif truth_table = [|true;false|] then
                    Inv (IO (undoubled <<< 1))
                else
                    // optimization: QM is a bit expensive, so check the cache.
                    let truth_table_string tt =
                        let sb = System.Text.StringBuilder ()
                        tt |> Array.iter (fun b -> sb.Append(if b then '1' else '0') |> ignore) // reversed string, but who cares as long as it's unique.
                        sb.ToString()
                    // OK, now I have a truth table.  This is the primary thing I'll operate over.
                    // I need to convert it into a minimal form first.
                    let half_size = truth_table.Length/2
                    let undoubled_false = Array.sub truth_table 0 half_size
                    let undoubled_true = Array.sub truth_table half_size half_size
                    let cachedQM tt =
                        let key = truth_table_string tt
                        if not (rewriteCache.ContainsKey key) then // let's do the QM!
                            // above are the 'true' and 'false' truth tables, split /a la/ Boole's expansion.
                            // Now to apply the Quine-McCluskey method of exact minimization.
                            // There's a great primer on this at http://www.allaboutcircuits.com/technical-articles/everything-about-the-quine-mccluskey-method/
                            let minimum =
                                try
                                    ``Quine-McCluskey``.quine_mccluskey tt
                                with
                                | _ ->
                                    printfn "QM failure, root=%d" idx
                                    reraise ()
                            rewriteCache.[key] <- minimum
                        rewriteCache.[key]
                    // Now map these strings, which represent minima, into an AIG that uses the given variables.
                    let final =
                        match cachedQM undoubled_false, cachedQM undoubled_true with
                        | [||], [||] -> Const false
                        | f, [||] ->
                            let subtree_f = mapBranchStrings variables f
                            Sub (subtree_f, Inv (IO (undoubled <<< 1)))
                        | [||], t ->
                            let subtree_t = mapBranchStrings variables t
                            Sub (subtree_t, IO (undoubled <<< 1))
                        | f, t ->
                            // now, put in the desired var on either side, up on top.
                            let subtree_f = mapBranchStrings variables f
                            let subtree_t = mapBranchStrings variables t
                            Inv (
                                Sub (
                                    Inv (Sub (IO (undoubled <<< 1), subtree_t)),
                                    Inv (Sub (Inv (IO (undoubled <<< 1)), subtree_f))
                            ))
                    final
            // CHECK!
            let ttable_check = evaluate_subtree variables diff
            if ttable_check <> truth_table then failwith "Correctness check FAILED."
            // and if all is good, then let's go on!
            let node = positiveNodeOf idx
            patch (node, diff)

    printfn "AAG output = %d, idx=%d, #modified=%d, #inverted=%d" aag.Output (idxOf aag.Output) modified.Count inverted.Count
    for i = 0 to idxOf aag.Output do
        // first, let's invert any inputs that need to be inverted.
        let a, b = modified.[i]
        let a' = if a >= ands_start && inverted.[idxOf a] then a ^^^ 1u else a
        let b' = if b >= ands_start && inverted.[idxOf b] then b ^^^ 1u else b
        modified.[i] <- (a',b')
        // now rewrite.
        //if i = 63 then
            //printfn "CHECK ME!"
        rewrite i
        // now check if the semantics are the same (v.expensive!)
        if false && dwlen=3u then
            let prelim_tt = { aag with Output=positiveNodeOf i } |> evaluate_aag
            let out = if inverted.[i] then positiveNodeOf i ^^^ 1u else positiveNodeOf i 

            let modified_aag = { Output=out; Ands=modified.ToArray() }
            let orig_aag = { aag with Output=out }
            let modified_tt = evaluate_aag modified_aag
            let orig_tt = evaluate_aag orig_aag
            if modified_tt <> orig_tt && modified_tt <> (Array.map not orig_tt) then
                let orig' = Option.get <| abc.AIGEvaluate(orig_aag, Strash)
                let orig'_tt = evaluate_aag orig'
                let modified' = Option.get <| abc.AIGEvaluate(modified_aag, Strash)
                let modified'_tt = evaluate_aag modified'
            //if not <| abc.AIGEquivalent(orig_aag, modified_aag, true) then
                failwithf "ERROR - NOT equivalent after modification of index %d" i

    let countWanteds (aag : AAG) =
        aag.Ands
        |> Array.fold (fun state (a,b) ->
            let cA = if (a >>> 1) = undoubled then 1 else 0
            let cB = if (b >>> 1) = undoubled then 1 else 0
            cA+cB+state
        ) 0

    printfn "output = %d (idx=%d), #modified=%d, #inverted=%d" aag.Output (idxOf aag.Output) modified.Count inverted.Count
    let out = if inverted.[idxOf aag.Output] then aag.Output ^^^ 1u else aag.Output
    let raw_aag = { Output=out; Ands=modified.ToArray() }
    abc.WriteAiger(aag, "c:\\Temp\\orig.aig")
    abc.WriteAiger(raw_aag, "c:\\Temp\\bubbled.aig")
    let output = Option.get <| abc.AIGEvaluate(raw_aag, Strash)
    abc.WriteAiger(output, "c:\\Temp\\mod.aig")

    let origCount = countWanteds aag
    let revisedCount = countWanteds output

    // some stats & data.
    printfn "Var %d.  Originally: %d instances of var.  Revised: %d instances (expected: 2)" undoubled origCount revisedCount
    let o_a, o_b = output.Ands.[idxOf output.Output]
    printfn "Output-node: %d : %d, %d" output.Output o_a o_b
    output.Ands
    |> Array.iteri (fun i (a,b) ->
        if (a >>> 1) = undoubled || (b >>> 1) = undoubled then
            printfn "Node %d : %d, %d" (positiveNodeOf i) a b
    )
    printfn "At end, (cumulative) cache has seen %d different functions." rewriteCache.Count
    assert (revisedCount=2)

    output



