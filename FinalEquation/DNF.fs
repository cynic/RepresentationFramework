namespace FinalEquation.DNF
open FinalEquation.CommonStructure

module DNFSet =
   open System.Collections.Generic
   //open SHA1.Helpers // used only for .Bits (right now, anyway...)

   let [<Literal>] MaxN = 1000 // maximum number of internal sets (a.k.a clauses) allowed

   (*
      Needs to represent a Set<Set<DNF>>.

      I'll use a uint64 for each one of the innermost sets.  Restricts me to 64 vars, but that's enough for now.
      What to use for the outermost set?  A linked-list?  No ... I want to avoid GCs as much as possible.
      Will use arrays instead.
      
      So Set<Set<DNF>> becomes:
         - int64[] (per-clause variable presence) +
         - int64[] (per-clause actual values) +
         - int[] (per-clause size)
         - int (number of terms)
   *)

   type BooleanVariable =
   | Positive of int
   | Negative of int
   with
      member __.Value = match __ with Positive n | Negative n -> n

   let positives = Array.init 512 (fun i -> Positive i)
   let negatives = Array.init 512 (fun i -> Negative i)

   type BooleanVariable
   with
      member __.Inverted with get () = match __ with Positive x -> negatives.[x] | Negative x -> positives.[x]

   type ClauseTestResult =
   | DoesNotExist = 0uy
   | ContainsPositive = 1uy
   | ContainsNegative = 2uy

   module ClauseFunctions =
      let calculateSize present =
         let mutable count = 0
         for i = 63 downto 0 do if present &&& (1UL <<< i) > 0UL then count <- count + 1
         count

      let calculateSizeWithLargestKnown present largest =
         let mutable count = 0
         for i = largest downto 0 do if present &&& (1UL <<< i) > 0UL then count <- count + 1
         count

      let calculateLargest present =
         let rec check n mask =
            if present &&& mask = 0UL then n
            else check (n+1) (mask <<< 1)
         check -1 0xFFFFFFFFFFFFFFFFUL

      let clause_var_tester = ref 1UL
      let clause_var_n = ref 0
      let clause_var_result = System.Collections.Generic.List()
      let variables present values =
            clause_var_tester := 1UL
            clause_var_n := 0
            clause_var_result.Clear()
            while !clause_var_tester > 0UL do
               if present &&& !clause_var_tester > 0UL then
                  if values &&& !clause_var_tester > 0UL then clause_var_result.Add positives.[!clause_var_n]
                  else clause_var_result.Add negatives.[!clause_var_n]
               clause_var_n := !clause_var_n + 1
               clause_var_tester := !clause_var_tester <<< 1
            clause_var_result

         (*
            We only need to check variables that are present in both.
            For each of those variables, we need to see whether the values are the same.
            Find the common variables by &&&'ing the 'present' arrays.
            Use the resulting mask to isolate the relevant values from one Clause.
            Now invert the other Clause's values, and mask it as well.
            If we XOR the two together, we should get the right result.
         *)
      let inline overlapExists (a : ^a) (b : ^b) =
         let mask = (^a : (member present : uint64) a) &&& (^b : (member present : uint64) b) // the items that are common to both.
         let a = (^a : (member values : uint64) a) &&& mask
         let b =  ~~~(^b : (member values : uint64) b) &&& mask
         a ^^^ b > 0UL

      let inline isXSubsetOfY (x : ^a) (y : ^b) =
         let mask = (^a : (member present : uint64) x) &&& (^b : (member present : uint64) y)
         ((^a : (member values : uint64) x) &&& mask) ^^^ (~~~(^b : (member values : uint64) y) &&& mask) = (^a : (member present : uint64) x)

      let inline isPowerOfTwo v = v <> 0UL && ((v &&& (~~~v + 1UL)) = v)

   [<Struct;StructuralEquality;StructuralComparison>]
   type Range =
      val start : uint64
      val ``end`` : uint64
      new (s, e) = { start = s; ``end`` = e }
   with
      override __.ToString () =
         sprintf "(%d, %d)" __.start __.``end``

   /// This should only be used internally.  Used by .Negated only, at present.
   [<Struct;StructuralEquality;StructuralComparison>]
   type MinimalClause =
      val present : uint64
      val values : uint64
      new (p, v) = { present = p; values = v }
   with
      override __.ToString () =
         __.Variables |> Seq.map (fun x ->
            match x with
            | Positive x -> sprintf "@%d" x
            | Negative x ->sprintf "¬@%d" x
         ) |> String.concat " ∧ "

      // this should be used mostly from stringification functions, not much more than that?
      member __.Variables with get () = ClauseFunctions.variables __.present __.values

      /// True if there is any overlap between this MinimalClause and the specified one
      member __.OverlapsWith (other : MinimalClause) = ClauseFunctions.overlapExists __ other

      /// True if this Clause is a subset of /other/
      member __.IsSubsetOf (other : MinimalClause) = ClauseFunctions.isXSubsetOfY __ other

   [<Struct;StructuralEquality;StructuralComparison>]
   type Clause =
      val size : int
      val present : uint64
      val values : uint64
      val largest : int
      new(vars : BooleanVariable seq) = {
         present =
            vars |> Seq.fold (fun state item -> state ||| (1UL <<< item.Value)) 0UL
         values =
            vars |> Seq.fold (fun state item -> match item with Positive n -> state ||| (1UL <<< n) | Negative n -> state) 0UL
         size = Seq.length vars
         largest = vars |> Seq.fold (fun state item -> max state item.Value) 0
      }
      new (var : BooleanVariable) = {
         present =
            match var with
            | Positive x | Negative x -> 1UL <<< x
         values =
            match var with
            | Positive x -> 1UL <<< x
            | Negative x -> 0UL
         size = 1
         largest = match var with Positive x | Negative x -> x
      }
      /// Don't use this unless you really, really, really know what you're doing.
      new(p : uint64, v : uint64, s : int, l : int) = { present = p; values = v; size = s; largest = l }

   with
      /// This *doesn't* result in allocation, whereas the default .Equals does.  No, I don't know why ... :-/.
      member __.EqualsClause (other : Clause) = __.present = other.present && __.values = other.values
      /// Same.  This *doesn't* result in allocation of GenericLessThanIntrinsic.
      member __.IsLessThan (other : Clause) =
         __.size < other.size ||
            (__.size = other.size &&
               (__.present < other.present ||
                  (__.present = other.present &&
                     (__.values < other.values ||
                        (__.values = other.values && __.largest < other.largest)
                     )
                  )
               )
            )

      override __.ToString () =
         __.Variables |> Seq.map (fun x ->
            match x with
            | Positive x -> sprintf "@%d" x
            | Negative x ->sprintf "¬@%d" x
         ) |> String.concat " ∧ "

      /// Returns a new clause with all the positives flipped to negatives, and vice versa
      member __.Inverted with get () = new Clause(__.present, ~~~__.values &&& __.present, __.size, __.largest)

      /// The number of terms in this clause
      member __.Count with get () = __.size

      /// The largest variable in this clause
      member __.Largest with get () = __.largest

      // this should be used mostly from stringification functions, not much more than that?
      member __.Variables with get () = ClauseFunctions.variables __.present __.values

      /// Returns a new Clause with the appropriate addition, or the existing Clause if no addition is necessary
      member __.Add var value =
         let bit = 1UL <<< var
         if __.present &&& bit > 0UL then
            let currentValue = __.values &&& bit > 0UL
            if currentValue = value then __
            else failwith "Will not add a contradiction: that is not supported."
         else
            if value then new Clause (__.present ||| bit, __.values ||| bit, __.size+1, max __.largest var)
            else new Clause (__.present ||| bit, __.values, __.size+1, max __.largest var)

      /// Returns a new Clause with the appropriate removal, or the existing Clause if no removal is necessary
      member __.Remove var =
         let bit = 1UL <<< var
         if __.present &&& bit > 0UL then
            let mask = ~~~(1UL <<< var)
            // removal affects the 'present' bitset AND the 'values' bitset.
            // This is done so that the logic for operations like 'union' can be simplified.
            let present = __.present &&& mask
            if var = __.largest then
               new Clause (present, __.values &&& mask, __.size-1, ClauseFunctions.calculateLargest present)
            else
               new Clause (present, __.values &&& mask, __.size-1, __.largest)
         else __

      member __.IsEmpty with get () = __.present = 0UL

      member __.TestClauseWith tester =
         if __.present &&& tester > 0UL then
            if __.values &&& tester > 0UL then ClauseTestResult.ContainsPositive
            else ClauseTestResult.ContainsNegative
         else
            ClauseTestResult.DoesNotExist

      /// True if there is any overlap between this Clause and the specified one
      member __.OverlapsWith other = ClauseFunctions.overlapExists __ other

      /// True if this Clause is a proper subset of /other/
      member __.IsProperSubsetOf (other : Clause) =
         (*
            for this to be true, this Clause must contain ONLY elements that exist in /other/,
            AND /other/ must contain at least one item which isn't in this Clause.
         *)
         let isSubset = ClauseFunctions.isXSubsetOfY __ other
         // now for this to be a *proper* subset, there must be at least one item in /other/ that doesn't exist in this Clause.
         // So, if I xor __.present and other.present together, I should get a non-zero result.
         isSubset && __.present ^^^ other.present > 0UL

      member __.SizeDiffIsOne (other : Clause) =
         let commonMask = __.present &&& other.present
         let a = __.values &&& commonMask
         let b = ~~~other.values &&& commonMask
         let subtractionMask = ~~~(a ^^^ b)
         let present = commonMask &&& subtractionMask
         ClauseFunctions.isPowerOfTwo present

      /// Returns a new clause with /other/ removed
      member __.Subtract (other : Clause) =
         let commonMask = __.present &&& other.present
         let a = __.values &&& commonMask
         let b = ~~~other.values &&& commonMask
         let subtractionMask = ~~~(a ^^^ b)
         let present = __.present &&& subtractionMask
         let largest = ClauseFunctions.calculateLargest present
         let size = ClauseFunctions.calculateSizeWithLargestKnown present largest
         new Clause(present, __.values &&& subtractionMask, size, largest)

      /// Returns the set union of two clauses
      member __.Union (other : Clause) =
         // this next line checks for the possibility of contradiction during the union, which nobody likes...
         assert (__.OverlapsWith other.Inverted = false)
         let present = __.present ||| other.present
         let values = __.values ||| other.values
         let largest = max __.largest other.largest
         let size = ClauseFunctions.calculateSizeWithLargestKnown present largest // I need to recount the bits set in 'present'.
         new Clause(present, values, size, largest)

   type MinimalClause
      with
         member __.ToClause () =
            let largest = ClauseFunctions.calculateLargest __.present
            new Clause(__.present, __.values, ClauseFunctions.calculateSizeWithLargestKnown __.present largest, largest)

   type DNFSet (initial_clauses : Clause seq) =
      let clauses =
         System.Collections.Generic.List(Seq.sort initial_clauses)
      let largestVarSeen = // largest var seen so far.
         ref (
            if Seq.isEmpty initial_clauses then 0
            else (initial_clauses |> Seq.maxBy (fun c -> c.Largest)).Largest
         )
      let negated_final = System.Collections.Generic.List()

      member val IsOne : bool = false with get, set
      member val IsZero : bool = false with get, set

      new () = new DNFSet(Array.empty)

      new (constantValue : bool) as __ =
         new DNFSet()
            then
               if constantValue then __.IsOne <- true
               else __.IsZero <- true
   (*
      Individual variables are read from the right, so @0 is the rightmost bit, @1 is the one to the left of that, etc.
      Individual clauses are read from the left, so clauses.[0] is the first set of terms, clauses.[1] is the next, etc.
      Using the top 6 bits of each clause to store the size, because it's easy.  Wastes 6 bits of 'present', but I don't care right now.
   *)

   (*
      All non-trivial methods take a 'dest', which is where the result is written to.
   *)
 
      interface System.IComparable with
         member __.CompareTo other = (__ :> System.IComparable<DNFSet>).CompareTo(other :?> DNFSet)
      interface System.IComparable<DNFSet> with
         member __.CompareTo other =
            if __.IsOne then
               __.IsOne.CompareTo other.IsOne
            elif __.IsZero then
               __.IsZero.CompareTo other.IsZero
            else
               Seq.compareWith (fun (a : Clause) (b : Clause) -> (a :> System.IComparable<Clause>).CompareTo(b))
                  __.Clauses
                  other.Clauses

   with
      override __.ToString () =
         if __.IsOne then "1"
         elif __.IsZero then "0"
         else __.Clauses |> Seq.map (sprintf "(%O)") |> String.concat " ∨ "

      member private __.clauses with get () = clauses and set (v : System.Collections.Generic.List<_>) = clauses.Clear(); clauses.AddRange(v)
      member private __.negated_final with get () = negated_final and set (v : System.Collections.Generic.List<_>) = negated_final.Clear(); negated_final.AddRange(v)
      member __.Clauses with get () = clauses
        
      /// If all terms are covered by the DNF, then the DNF reduces to 1.
      static let reducesToOne_clause_coverage = System.Collections.Generic.List()
      member __.ReducesToOne
         with get () =
            if __.IsOne then true
            elif __.IsZero then false
            elif __.Clauses |> Seq.exists (fun c -> c.Count = 0) then true
            elif __.Clauses.Count = 0 then true // if there are no terms, then by definition all terms are covered.  Yes??
            else
               // get all the variables that are present
               let allVars =
                  let mutable result = 0UL
                  for i = 0 to __.Clauses.Count-1 do
                     result <- result ||| __.Clauses.[i].present
                  result
               // get the hamming weight via Kernighan's method, http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetKernighan
               let hammingWeight = // this is the number of variables that exist in this DNF
                  let mutable to_check = allVars
                  let mutable result = 0
                  while to_check > 0UL do
                     result <- result+1
                     to_check <- to_check &&& (to_check-1UL)
                  result
               let initialRange = new Range(0UL, (2. ** float hammingWeight |> uint64)-1UL)
               let top_of (r : Range) = new Range((r.``end``-r.start)/2UL+1UL+r.start, r.``end``)
               let bottom_of (r : Range) = new Range(r.start, (r.``end``-r.start)/2UL+r.start)
               reducesToOne_clause_coverage.Clear()
               let merge (item : Range) =
                  if reducesToOne_clause_coverage.Count = 0 then
                     reducesToOne_clause_coverage.Add item // ta da!  Done.
                  else
                     let pos = reducesToOne_clause_coverage.BinarySearch item
                     if pos < 0 then // hm, doesn't exist.
                        match ~~~pos with
                        | 0 -> // check the existing [0] value for possible merge potential
                           let neighbourTop = reducesToOne_clause_coverage.[0]
                           if item.``end``+1UL >= neighbourTop.start then
                              // merge it
                              reducesToOne_clause_coverage.[0] <- new Range(min item.start neighbourTop.start, max item.``end`` neighbourTop.``end``)
                           else
                              reducesToOne_clause_coverage.Insert(0, item)
                        | x when x = reducesToOne_clause_coverage.Count ->
                           let neighbourBottom = reducesToOne_clause_coverage.[x-1]
                           if item.start-1UL <= neighbourBottom.``end`` then
                              // merge it
                              reducesToOne_clause_coverage.[x-1] <- new Range(min item.start neighbourBottom.start, max item.``end`` neighbourBottom.``end``)
                           else
                              reducesToOne_clause_coverage.Add item
                        | x -> // somewhere in the middle...
                           let neighbourBottom = reducesToOne_clause_coverage.[x-1]
                           let neighbourTop = reducesToOne_clause_coverage.[x]
                           if neighbourBottom.``end``+1UL >= item.start && neighbourTop.start-1UL <= item.``end`` then
                              // This is sandwiched directly in-between.  Make a single contiguous region.
                              reducesToOne_clause_coverage.[x-1] <- new Range(min neighbourBottom.start item.start, max neighbourTop.``end`` item.``end``)
                              reducesToOne_clause_coverage.RemoveAt x
                           elif neighbourBottom.``end``+1UL >= item.start then // overlaps the neighbour beneath
                              reducesToOne_clause_coverage.[x-1] <- new Range(min neighbourBottom.start item.start, max neighbourBottom.``end`` item.``end``)
                           elif neighbourTop.start-1UL <= item.``end`` then // overlaps the neighbour above
                              reducesToOne_clause_coverage.[x] <- new Range(min neighbourTop.start item.start, max neighbourTop.``end`` item.``end``)
                           else
                              reducesToOne_clause_coverage.Insert(x, item) // no overlaps.
                     //else () // already exists? Well, nothing to do, then.
               let rec clause_coverage j (c : Clause) (range : Range) =
                  if j > c.largest then
                     // we're done here.  I should merge the /start/ and /end/ into the list.
                     merge range
                  else
                     let tester = 1UL <<< j
                     if allVars &&& tester > 0UL then
                        if c.present &&& tester > 0UL then
                           let half_range =
                              // if it's positive, then I want the top-half.
                              if c.values &&& tester > 0UL then top_of range
                              // if it's negative, then I want the bottom-half
                              else bottom_of range
                           clause_coverage (j+1) c half_range
                        else
                           // it's present in allVars, but not in .present.  So I need to split.
                           let bottom_range = bottom_of range
                           let top_range = top_of range
                           clause_coverage (j+1) c bottom_range
                           clause_coverage (j+1) c top_range
                     else
                        clause_coverage (j+1) c range
               for i = 0 to __.Clauses.Count-1 do
                  clause_coverage 0 __.Clauses.[i] initialRange
               reducesToOne_clause_coverage.Count = 1 && reducesToOne_clause_coverage.[0] = initialRange

      /// The number of clauses in the DNFSet.  This is NOT the same as .Clauses.Length, which gives capacity instead!
      member __.NumberOfClauses with get () = clauses.Count
      member private __.LargestVarSeen
         with get () = !largestVarSeen
         and set v = largestVarSeen := v

      member __.Clear () =
         clauses.Clear ()
         largestVarSeen := 0
         __.IsOne <- false
         __.IsZero <- false
         negated_final.Clear()

      member __.ContainsClause (x : Clause) = clauses.BinarySearch(x) >= 0

      member __.CloneTo (dest : DNFSet) =
         dest.clauses.Clear()
         dest.negated_final.Clear()
         for c in clauses do dest.clauses.Add c
         for x in negated_final do dest.negated_final.Add x
         dest.LargestVarSeen <- !largestVarSeen
         dest.IsOne <- __.IsOne
         dest.IsZero <- __.IsZero

      member __.AddClause c (dest : DNFSet) =
         __.CloneTo dest
         let bsResult = __.clauses.BinarySearch(c)
         if bsResult < 0 then // it doesn't already exist
            dest.LargestVarSeen <- max c.Largest !largestVarSeen
            dest.clauses.Insert(~~~bsResult, c)

      member __.AddClause_SELF c =
         let bsResult = __.clauses.BinarySearch(c)
         if bsResult < 0 then // it doesn't already exist
            largestVarSeen := max c.Largest !largestVarSeen
            __.clauses.Insert(~~~bsResult, c)
            negated_final.Clear()

      member __.RemoveClause (c : Clause) (dest : DNFSet) =
         __.CloneTo dest
         let bsResult = __.clauses.BinarySearch(c)
         if bsResult >= 0 then
            dest.clauses.RemoveAt bsResult
            let largest =
               if c.Largest < !largestVarSeen then !largestVarSeen
               elif dest.clauses.Count = 0 then 0
               else // urgh, now I probably need to do a full scan...
                  let mutable largest = 0
                  for x in dest.Clauses do largest <- max largest x.Largest
                  largest
            dest.LargestVarSeen <- largest

      member __.RemoveClause_SELF (c : Clause) =
         let bsResult = __.clauses.BinarySearch(c)
         if bsResult >= 0 then
            __.clauses.RemoveAt bsResult
            let largest =
               if c.Largest < !largestVarSeen then !largestVarSeen
               elif __.clauses.Count = 0 then 0
               else // urgh, now I probably need to do a full scan...
                  let mutable largest = 0
                  for x in __.Clauses do largest <- max largest x.Largest
                  largest
            largestVarSeen := largest
            negated_final.Clear()

      /// Returns the set of all clauses containing @v
      member __.ClausesContaining (v : BooleanVariable) (dest : DNFSet) =
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         let mutable largest = 0
         let tester = match v with Positive n | Negative n -> 1UL <<< n
         let grabPositive = match v with Positive n -> true | Negative n -> false
         dest.Clear()
         for i = 0 to clauses.Count-1 do
            match clauses.[i].TestClauseWith tester with
            | ClauseTestResult.ContainsPositive ->
               if grabPositive then
                  dest.clauses.Add clauses.[i]
                  largest <- max largest clauses.[i].Largest
            | ClauseTestResult.ContainsNegative ->
               if not grabPositive then
                  dest.clauses.Add clauses.[i]
                  largest <- max largest clauses.[i].Largest
            | _ -> ()
         dest.LargestVarSeen <- largest
         
      /// Returns the set of all clauses containing @v, whether in positive or negative form
      member __.ClausesContainingAny (v : int) (dest : DNFSet) =
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         let mutable largest = 0
         let tester = 1UL <<< v
         dest.Clear()
         for clause in __.Clauses do
            match clause.TestClauseWith tester with
            | ClauseTestResult.ContainsPositive | ClauseTestResult.ContainsNegative ->
                  dest.clauses.Add clause
                  largest <- max largest clause.Largest
            | _ -> ()
         dest.LargestVarSeen <- largest

      static let vpos_neg_tester = ref 1UL
      static let vpos_neg_n = ref 0
      static let vpos_neg_return = System.Collections.Generic.List()
      /// Returns the Positive form of variables which are present in more than one clause, AND which have both Positive and Negative variants
      member __.``variables with positive and negative variants`` =
         let mutable zeroVariantPresent = 0UL
         let mutable oneVariantPresent = 0UL
         for var = 0 to !largestVarSeen do
            let tester = 1UL <<< var
            for x = 0 to clauses.Count-1 do
               match clauses.[x].TestClauseWith tester with
               | ClauseTestResult.ContainsNegative -> zeroVariantPresent <- zeroVariantPresent ||| tester
               | ClauseTestResult.ContainsPositive -> oneVariantPresent <- oneVariantPresent ||| tester
               | _ -> ()
         let result = oneVariantPresent &&& zeroVariantPresent
         vpos_neg_tester := 1UL
         vpos_neg_n := 0
         vpos_neg_return.Clear()
         while !vpos_neg_tester > 0UL do
            if result &&& !vpos_neg_tester > 0UL then vpos_neg_return.Add !vpos_neg_n
            vpos_neg_n := !vpos_neg_n + 1
            vpos_neg_tester := !vpos_neg_tester <<< 1
         vpos_neg_return
         
      member __.Where f (dest : DNFSet) =
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         let mutable largest = 0
         dest.Clear()
         for clause in __.Clauses do
            if f clause then
               dest.clauses.Add clause
               largest <- max largest clause.Largest
         dest.LargestVarSeen <- largest

      /// Written to replace a call to .Where, and remove an allocation
      member __.SuitableForDiscovery1 (t0 : Clause) (neg_item : Clause) (dest : DNFSet) =
         (*
            discovery1_dnfset_0.Where (fun t1 ->
               t1.Count <> t0.Count && t1.OverlapsWith neg_item && t0.OverlapsWith t1
            ) discovery1_dnfset_1
         *)
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         let mutable largest = 0
         dest.Clear()
         for t1 in __.Clauses do
            if t1.Count <> t0.Count && t1.OverlapsWith neg_item && t0.OverlapsWith t1 && t0.SizeDiffIsOne t1 then
               dest.clauses.Add t1
               largest <- max largest t1.Largest
         dest.LargestVarSeen <- largest

      /// Enacts the set union of two DNFSets
      member __.Union (other : DNFSet) (dest : DNFSet) =
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         assert (other.IsOne = false)
         assert (other.IsZero = false)
         dest.clauses.Clear()
         dest.negated_final.Clear()
         let rec merge i j =
            if i >= __.clauses.Count && j >= other.Clauses.Count then
                // done!
               dest.LargestVarSeen <- max !largestVarSeen other.LargestVarSeen
               ()
            else
               if i >= __.clauses.Count || (j < other.clauses.Count && other.clauses.[j].IsLessThan clauses.[i]) then
                  dest.clauses.Add other.clauses.[j] // just add from /other/
                  merge i (j+1)
               elif j >= other.clauses.Count || (i < __.clauses.Count && clauses.[i].IsLessThan other.clauses.[j]) then
                  dest.clauses.Add clauses.[i]
                  merge (i+1) j
               else // clauses.[i] and other.Clauses.[j] must be equivalent if we're here
                  assert (clauses.[i] = other.clauses.[j]) // 'cos there's nothing wrong with paranoia :D
                  dest.clauses.Add clauses.[i]
                  merge (i+1) (j+1)
         merge 0 0

      /// True if there is any overlap between this DNFSet and the specified one
      member __.OverlapsWith (other : DNFSet) =
         let rec check i j =
            if i >= __.clauses.Count || j >= other.clauses.Count then
               false
            else
               if clauses.[i].Equals other.clauses.[j] then true
               elif clauses.[i].IsLessThan other.clauses.[j] then check (i+1) j
               else check i (j+1)
         check 0 0

      /// Returns the size of the longest clause in the DNF expression
      member __.SizeOfLongestClause
         with get () =
            let mutable longest = 0
            for c in clauses do longest <- max longest c.Count
            longest

      (*
         Given a Clause X, I need to remove all Clauses which X is a 'proper subset' of.
         In other words, all clauses which contain X AND at least one other term.
      *)
      /// Given /c/, remove all clauses which contain /c/ and at least one other term
      member __.AbsorbUsing (c : Clause) =
         let mutable largest = 0
         for i = clauses.Count-1 downto 0 do
            if c.IsProperSubsetOf clauses.[i] then
               // remove it from the result set.
               clauses.RemoveAt i
            else
               largest <- max largest clauses.[i].Largest
         largestVarSeen := largest
         
      /// apply negative absorption using /c/: (¬c ∨ (c ∧ b) = (¬c ∨ b))
      member __.NegativeAbsorbUsing (c : Clause) =
         // negative absorption only works in DNF when /c/ is a single-var term
         if c.Count = 1 then
            let invert = c.Inverted
            let mutable largest = 0
            for i = clauses.Count-1 downto 0 do
               // ... hmm ... or maybe I should just do a subtraction in any case ... to go faster, do less?
               if invert.OverlapsWith clauses.[i] then
                  let modified = clauses.[i].Subtract invert // remove the item from the clause.
                  if not <| __.ContainsClause modified then
                     clauses.[i] <- modified // only replace if an equivalent clause doesn't already exist
                     largest <- max largest clauses.[i].Largest
                  else
                     clauses.RemoveAt i
               else
                  largest <- max largest clauses.[i].Largest
            clauses.Sort()
            largestVarSeen := largest
      
      member __.EvaluateWith (datawords : uint32[]) =
         if __.IsOne then true
         elif __.IsZero then false
         else
            let mutable result = false
            let rec doCheck idx =
               if idx = clauses.Count then
                  false
               else
                  let c = clauses.[idx]
                  let mutable intermediate = true
                  for v in c.Variables do
                     intermediate <- intermediate &&
                        match v with
                        | Positive x -> datawords.[x/32].[x%32]
                        | Negative x -> not datawords.[x/32].[x%32]
                  if intermediate then true
                  else doCheck (idx+1)
            doCheck 0

      static let dnfB = System.Collections.Generic.List()
      static let dnfB_largests = System.Collections.Generic.List()
      static let negated_result = System.Collections.Generic.List()

      member __.Complement_SELF () =
         for i = 0 to clauses.Count-1 do
            let c = clauses.[i]
            clauses.[i] <- new Clause(c.present, (c.values ^^^ 0xFFFFFFFFFFFFFFFFUL) &&& c.present, c.size, c.largest)

      member __.SerializedString =
         if __.IsOne then "1"
         elif __.IsZero then "0"
         else
            sprintf "%d|%s|%s"
               !largestVarSeen
               (__.clauses |> Seq.map (fun c ->
                  sprintf "0x%x~0x%x~%d~%d" c.present c.values c.size c.largest
               ) |> String.concat " ")
               (__.negated_final |> Seq.map (fun (nc : Clause) ->
                  sprintf "0x%x~0x%x~%d~%d" nc.present nc.values nc.size nc.largest
               ) |> String.concat " ")

      static member CreateFromSerialized (s : string) =
         match s with
         | "0" -> new DNFSet(false)
         | "1" -> new DNFSet(true)
         | _ ->
            let result = new DNFSet()
            let split = s.Split [|'|'|]
            let largest = int split.[0]
            let clausesIn (s : string) =
               if s.Length = 0 then
                  Seq.empty
               else
                  s.Split [|' '|]
                  |> Seq.map (fun s ->
                     let datum = s.Split([|'~'|])
                     new Clause(uint64 datum.[0], uint64 datum.[1], int datum.[2], int datum.[3])
                  )
            let clauses = clausesIn split.[1]
            let finals = clausesIn split.[2]
            result.LargestVarSeen <- largest
            result.clauses <- System.Collections.Generic.List(clauses)
            result.negated_final <- System.Collections.Generic.List(finals)
            result

      member __.Negated (dest : DNFSet) =
         // setup...
         assert (__.IsOne = false)
         assert (__.IsZero = false)
         assert (__.clauses.Count > 0)
#if DEBUG
         let mutable __debug_this_code = false
         let mutable trap_end = false
         let mutable t_start = System.DateTime.Now
#endif
         dest.Clear ()
         if negated_final.Count > 0 then
            for x in negated_final do dest.clauses.Add x
            dest.LargestVarSeen <- !largestVarSeen
         else
            //let sw = System.Diagnostics.Stopwatch()
            //System.Console.WriteLine("Negated-form for DNF with {0} clauses", __.NumberOfClauses)
            //sw.Start()
            (*
               The typical way has been to get a DNFSet of each individual (negated) variable in each clause, and then AND them together.
            *)
            negated_result.Clear()
   (*
         for x in dnfA.Clauses do
            let contradictors = x.Inverted
            for b in dnfB.Clauses do
               if not <| contradictors.OverlapsWith b then
                  dest.AddClause_SELF (x.Union b)
   *)
            // start off with the very first clause, if we're right at the beginning.
            for i = 0 to clauses.Count-1 do
#if DEBUG
               if (System.DateTime.Now-t_start).TotalSeconds > 20. then
                  trap_end <- true
                  System.Diagnostics.Debugger.Break ()
                  t_start <- System.DateTime.Now
#endif
               dnfB.Clear()
               dnfB_largests.Clear()
               let c = clauses.[i]
               let mutable var_tester = 1UL
               let mutable largest = 0
               let stop = 1UL <<< c.largest
               while var_tester <= stop do
                  if c.present &&& var_tester > 0UL then
                     dnfB.Add (new MinimalClause(var_tester, ~~~c.values &&& var_tester))
                     dnfB_largests.Add largest
                  var_tester <- var_tester <<< 1
                  largest <- largest + 1

               if i = 0 then
                  for j = 0 to dnfB.Count-1 do negated_result.Add (new Clause(dnfB.[j].present, dnfB.[j].values, 1, dnfB_largests.[j]))
               else
#if DEBUG
                  if __debug_this_code then System.Diagnostics.Debugger.Break()
#endif
                  for j = negated_result.Count-1 downto 0 do
                     let x = negated_result.[j]
                     negated_result.RemoveAt j
                     let contradictors = new MinimalClause(x.present, ~~~x.values &&& x.present)
                     for k = 0 to dnfB.Count-1 do
                        let b = dnfB.[k]
                        if not (ClauseFunctions.overlapExists contradictors b) then // check for annihilation
                           if x.present &&& b.present > 0UL then // check for idempotence
                              let nr_idx = negated_result.BinarySearch x
                              if nr_idx < 0 then
                                 negated_result.Insert(~~~nr_idx, x)
                           else
                              let result = new Clause(x.present ||| b.present, x.values ||| b.values, x.size+1, max x.largest dnfB_largests.[k])
                              let nr_idx = negated_result.BinarySearch result
                              if nr_idx < 0 then
                                 negated_result.Insert(~~~nr_idx, result)
                  // ... and here is where I do absorption.
                  let mutable selected = negated_result.Count-2
#if DEBUG
                  if __debug_this_code then System.Diagnostics.Debugger.Break()
#endif
                  if negated_result.Count > 1 then
(*
                     let mutable selectedSize =
                        let mutable start = negated_result.[negated_result.Count-1].size
                        for i = start downto 0 do
                           if negated_result.[i] < negated_result.[selected]
                           negated_result.[negated_result.Count-2].size
*)
                     //while negated_result.[selected].size > selected do
                     while selected >= 0 do
                        let c : Clause = negated_result.[selected]
                        for i = negated_result.Count-1 downto (selected+1) do
                           let o = negated_result.[i]
                           let mask = c.present &&& o.present
                           if (c.values &&& mask) ^^^ (~~~o.values &&& mask) = c.present then
                              negated_result.RemoveAt i // remove it from the result set.
                        selected <- min (selected-1) (negated_result.Count-1)

#if DEBUG
            if __debug_this_code then System.Diagnostics.Debugger.Break()
#endif
            for x in negated_result do
               negated_final.Add x
               dest.clauses.Add x
            dest.LargestVarSeen <- !largestVarSeen
            //sw.Stop()
            //System.Console.WriteLine("Negated form calculated in {0}", sw.Elapsed);
#if DEBUG
            if __debug_this_code || trap_end then System.Diagnostics.Debugger.Break()
#endif
            //System.Diagnostics.Debugger.Break()
            //System.Console.WriteLine("Done")

   let dnfZero = new DNFSet(false)
   let dnfOne = new DNFSet(true)





open DNFSet

type DisjunctiveNormalForm() =
    let elimination_dnfset_0 = new DNFSet ()
    let elimination_dnfset_1 = new DNFSet ()
    let elimination_dnfset_2 = new DNFSet ()
    let elimination_removal_made = ref false

    /// Apply elimination ((a ∧ b) ∨ (¬a ∧ b) = b) to /xs/
    let elimination (xs : DNFSet) =
       let relevant = xs.``variables with positive and negative variants``
       if relevant.Count > 0 then // if there's nothing relevant here, skip it.
          xs.CloneTo elimination_dnfset_0
          // ok, now we have the set of positive variables which have negative counterparts.
          for v_idx = 0 to relevant.Count-1 do
             let v = relevant.[v_idx]
             xs.ClausesContainingAny v elimination_dnfset_2
             for s_idx = 0 to elimination_dnfset_2.Clauses.Count-1 do
                let s = elimination_dnfset_2.Clauses.[s_idx]
                let key = s.Remove v
                elimination_removal_made := false
                for c_idx = s_idx+1 to elimination_dnfset_2.Clauses.Count-1 do
                   let c = elimination_dnfset_2.Clauses.[c_idx]
                   let candidate = c.Remove v
                   if candidate.EqualsClause key then // don't compare to myself; and I should be able to replace /s/ and /c/ with /key/
                      elimination_dnfset_0.RemoveClause_SELF c
                      elimination_removal_made := true
                if !elimination_removal_made then
                   elimination_dnfset_0.RemoveClause_SELF s
                   elimination_dnfset_0.AddClause_SELF key
          elimination_dnfset_0.CloneTo xs

    let discovery1_dnfset_0 = new DNFSet()
    let discovery1_dnfset_1 = new DNFSet()
    let discovery1_dnfset_2 = new DNFSet()
    let discovery1_dnfset_3 = new DNFSet()
    /// (a ∧ b ∧ c) ∨ (a ∧ ¬b) = (a ∧ c) ∨ (a ∧ ¬b).  Don't know what to call this fact, but sure there must be a name for it...
    let discovery1 (xs : DNFSet) =
       (*
          Conditions:

          o The two terms MUST have 1 or more vars in common.
          o The two terms MUST have different lengths.
          o Exactly 1 variable MUST  be inverted between the two terms.
          o Except for the inverted variable, the shorter term must contain no terms that do not also occur in the longer term.
       *)
       // ok, now we have the set of positive variables which have negative counterparts.
       let mutable relevant = xs.``variables with positive and negative variants``
       if relevant.Count > 0 then // if nothing relevant, skip it.
          xs.CloneTo discovery1_dnfset_0
          let mutable i = 0
          while i < relevant.Count do
             let v = relevant.[i]
             let item = positives.[v]
             // find all terms that contain /v/.
             discovery1_dnfset_0.ClausesContaining item discovery1_dnfset_3
             let mutable replacements_made = false
             for t0 in discovery1_dnfset_3.Clauses do
                // find all terms that have different lengths, AND contain ¬/v/, AND have >=1 var in common
                let neg_item = Clause(item).Inverted
                (*
                discovery1_dnfset_0.Where (fun t1 ->
                   t1.Count <> t0.Count && t1.OverlapsWith neg_item && t0.OverlapsWith t1
                ) discovery1_dnfset_1
                *)
                discovery1_dnfset_0.SuitableForDiscovery1 t0 neg_item discovery1_dnfset_1 
                // ok, 3 conditions down.  Still need to check the 4th condition.
                for t1 in discovery1_dnfset_1.Clauses do
                   if t0.Count < t1.Count then
                      if t0.Subtract(t1).Count = 1 then
                         // ok, do replacement.
                         let replacement = t1.Remove v
                         discovery1_dnfset_0.RemoveClause_SELF t1
                         discovery1_dnfset_0.AddClause_SELF replacement
                         replacements_made <- true
                   else
                      if t1.Subtract(t0).Count = 1 then
                         // ok, do replacement.
                         let replacement = t0.Remove v
                         discovery1_dnfset_0.RemoveClause_SELF t0
                         discovery1_dnfset_0.AddClause_SELF replacement
                         replacements_made <- true
             if replacements_made then
                // reevaluate 'relevant', and start up again.
                relevant <- discovery1_dnfset_0.``variables with positive and negative variants``
                i <- 0
             else
                i <- i + 1
          discovery1_dnfset_0.CloneTo xs

    /// Apply absorption laws (a ∨ (a ∧ b) = a) and (¬a ∨ (a ∧ b) = (¬a ∨ b)) to /xs/
    let absorption (xs : DNFSet) =
       let maxCount = xs.SizeOfLongestClause
       let absorb (item : Clause) =
          if item.Count < maxCount then
             // positive absorption
             xs.AbsorbUsing item
             // now apply negative absorption, (¬a ∨ (a ∧ b) = (¬a ∨ b))
             xs.NegativeAbsorbUsing item
       let mutable i = 0
       while i < xs.Clauses.Count do
          absorb xs.Clauses.[i]
          i <- min (xs.Clauses.Count) (i+1)

    let consensus_dnfset_0 = new DNFSet ()
    let consensus_dnfset_1 = new DNFSet ()
    let consensus_dnfset_2 = new DNFSet ()
    /// Removes a particular variety of extra covering from the DNF
    let consensusTheorem (s : DNFSet) =
       (*
          An extra covering must contain the same variables as exist in other coverings,
          PLUS variables that basically evaluate to the truth.
          e.g. in (a ∧ ¬b) ∨ (¬a ∧ ¬c) ∨ (¬b ∧ ¬c), the covering (¬b ∧ ¬c) is unnecessary.

          My way of removing extra coverings is as follows:

          1. Find all the variables that have positive AND negative versions (e.g. a/¬a).
             Just keep the positive versions (would work just as well with negative versions
             only, as long as it's one or the other).
          2. For each variable /u/ and state /s/, (e.g. a)
             1. For each term /v/ which contains a /u/, (e.g. a∧¬b)
                1. For each term /w/ which contains ¬/u/, (e.g. ¬a∧¬c)
                   1. Union /v/ and /w/, and remove /u/ and ¬/u/, to obtain /x/. (e.g. (a∧¬b) ∪ (¬a∧¬c) = a∧¬a∧¬b∧¬c => ¬b∧¬c)
                   2. Remove /x/ from the state; it is extraneous.
                   3. Now pass the new /s/ up to (2).
    *)
       // (1)
       let check_u u_value = // (2) // 'state' is /remExtra_dnfset_0/
          let not_u = negatives.[u_value]
          let check_v_term (v : Clause) = // (2.1) //
             let check_w_term (w : Clause) = // (2.1.1)
                let mod_v = v.Remove u_value
                let mod_w = w.Remove u_value
                if not <| mod_v.OverlapsWith mod_w.Inverted then
                   let x = mod_v.Union mod_w // (2.1.1.1)
                   consensus_dnfset_0.RemoveClause_SELF x // (2.1.1.2 & 2.1.1.3)
             consensus_dnfset_0.ClausesContaining not_u consensus_dnfset_2
             for x in consensus_dnfset_2.Clauses do check_w_term x
          consensus_dnfset_0.ClausesContaining positives.[u_value] consensus_dnfset_1
          for x in consensus_dnfset_1.Clauses do check_v_term x
       s.CloneTo consensus_dnfset_0
       for x in s.``variables with positive and negative variants`` do check_u x
       consensus_dnfset_0.CloneTo s

    (*
       Details of how to use the _and, _or, and _not have changed.

       - After being called, if the result is not a complex expression, XX_dnfset_0 will have 0 terms.
         Otherwise, XX_dnfset_0 will hold the result.
    *)

    let storage_dnfset_0 = new DNFSet ()

    let not_dnfset_0 = new DNFSet ()
    let not_dnfset_1 = new DNFSet ()
    let not_dnfset_subarray = Array.init DNFSet.MaxN (fun _ -> new DNFSet ())

    let _not (x : DNFSet) (dest : DNFSet) =
       if x.IsOne then dnfZero.CloneTo dest
       elif x.IsZero then dnfOne.CloneTo dest
       elif x.NumberOfClauses = 0 then dest.Clear()
       else
          x.Negated dest
          //System.Diagnostics.Debugger.Break()
          //absorption dest
          //elimination dest
          //discovery1 dest
          consensusTheorem dest
          //System.Diagnostics.Debugger.Break()
    #if DEBUG
          //if !debug then System.Console.WriteLine("not ({0}) => {1}", x, dest)
    #endif

    let and_dnfset_0 = new DNFSet()

    let _and (dnfA : DNFSet) (dnfB : DNFSet) (dest : DNFSet) =
       if dnfA.IsZero || dnfB.IsZero then
          dnfZero.CloneTo dest
       elif dnfA.IsOne && dnfB.IsOne then
          dnfOne.CloneTo dest
       elif dnfA.IsOne then
          dnfB.CloneTo dest
       elif dnfB.IsOne then
          dnfA.CloneTo dest
       else
          dest.Clear()
          for x in dnfA.Clauses do
             let contradictors = x.Inverted
             for b in dnfB.Clauses do
                if not <| contradictors.OverlapsWith b then
                   dest.AddClause_SELF (x.Union b)
          if dest.NumberOfClauses = 0 then
             dnfZero.CloneTo dest
          else
             absorption dest
             discovery1 dest
             consensusTheorem dest
    #if DEBUG
             //if !debug then System.Console.WriteLine("({0}) and ({1}) => {2}", dnfA, dnfB, dest)
    #endif

    let or_dnfset_0 = new DNFSet ()

    let _or (dnfA : DNFSet) (dnfB : DNFSet) (dest : DNFSet) =
       if dnfA.IsOne || dnfB.IsOne then
          dnfOne.CloneTo dest
       elif dnfA.IsZero && dnfB.IsZero then
          dnfZero.CloneTo dest
       elif dnfA.IsZero then
          dnfB.CloneTo dest
       elif dnfB.IsZero then
          dnfA.CloneTo dest
       elif dnfA = dnfB then
          dnfA.CloneTo dest
       else
          dnfA.Union dnfB or_dnfset_0
          absorption or_dnfset_0
          elimination or_dnfset_0
          discovery1 or_dnfset_0
          consensusTheorem or_dnfset_0
          if or_dnfset_0.ReducesToOne then
             dnfOne.CloneTo dest
          else
    #if DEBUG
             //if !debug then System.Console.WriteLine("({0}) or ({1}) => {2}", dnfA, dnfB, or_dnfset_0)
    #endif
             or_dnfset_0.CloneTo dest
       
    let xor_dnfset_0 = new DNFSet()
    let xor_dnfset_1 = new DNFSet()
    let xor_dnfset_2 = new DNFSet()

    let rec xor (a : DNFSet) (b : DNFSet) (dest : DNFSet) =
       if a.IsZero && b.IsZero || a.IsOne && b.IsOne then
          dnfZero.CloneTo dest
       elif a.IsZero then
          b.CloneTo dest
       elif b.IsZero then
          a.CloneTo dest
       elif a.IsOne then
          _not b dest
          if dest.NumberOfClauses = 0 then dnfZero.CloneTo dest
       elif b.IsOne then
          _not a dest
          if dest.NumberOfClauses = 0 then dnfZero.CloneTo dest
       else
          // all of these 'ifs' are because xor might be passed inaccurate DNFs.
          _not b xor_dnfset_0 // not_b
          if xor_dnfset_0.NumberOfClauses = 0 then
             xor a dnfOne dest
          else
             _and a xor_dnfset_0 xor_dnfset_1 // a and not_b
             _not a xor_dnfset_0 // not_a
             if xor_dnfset_0.NumberOfClauses = 0 then
                xor dnfOne b dest
             else
                _and b xor_dnfset_0 dest // b and not_a
                let _dest = new DNFSet()
                dest.CloneTo(_dest)
                _or _dest xor_dnfset_1 dest
          //System.Console.WriteLine("{0} ⊕ {1} => {2}", a, b, dest)

    interface IRepresentation<DNFSet> with
        member __.Evaluate data point = point.EvaluateWith data                
        member __.EvaluationCache data = None
        member __.And a b =
            let dest = new DNFSet()
            _and a b dest
            dest
        member __.Or a b =
            let dest = new DNFSet()
            _or a b dest
            dest
        member __.Not x =
            let dest = new DNFSet()
            _not x dest
            dest
        member __.Xor a b =
            let dest = new DNFSet()
            xor a b dest
            dest
        member __.MakeVariable v = DNFSet [|Clause positives.[int v]|]
        member __.Constants with get () = { One=dnfOne; Zero=dnfZero }
        member __.IsOne x = x.IsOne
        member __.IsZero x = x.IsZero
        member __.Dispose () = ()

