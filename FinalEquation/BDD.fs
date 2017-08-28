module FinalEquation.BDD

module Reordering =
    /// Leave the reordering method unchanged.
    let [<Literal>] SameAsBefore = 0
    /// No reordering should be performed.
    let [<Literal>] None = 1
    /// Randomly swap pairs of variables, retaining the best series of sways.  # of pairs chosen is same as the # of variables.
    let [<Literal>] RandomSwaps = 2
    /// Just like RandomSwaps, but pairs are chosen so that first is above the closest-to-root variable with largest number of nodes, and second is just below the first.
    let [<Literal>] RandomPivoting = 3
    /// Rudell's sifting algorithm, variables are sifted up & down to see where they do "best".  See also Cudd_[Read|Set]SiftMaxVar and Cudd_[Read|Set]MaxGrowth.
    let [<Literal>] Sift = 4
    /// Like Sift, but go on until convergence.
    let [<Literal>] SiftConverge = 5
    /// Similar to Sift, but also tests variables for symmetry, and if they are symmetric, sifting continues with the variables grouped.
    let [<Literal>] SiftSymmetric = 6
    /// Like SiftSymmetric, but go on until convergence.
    let [<Literal>] SiftSymmetricConverge = 7
    /// "Window permutation approach" (see papers by Fujita and by Ishiura).  Size of the window is 2.
    let [<Literal>] WindowSize2 = 8
    /// "Window permutation approach" (see papers by Fujita and by Ishiura).  Size of the window is 3.
    let [<Literal>] WindowSize3 = 9
    /// "Window permutation approach" (see papers by Fujita and by Ishiura).  Size of the window is 4.
    let [<Literal>] WindowSize4 = 10
    /// Like WindowSize2, but go on until convergence.
    let [<Literal>] WindowSize2Converge = 11
    /// Like WindowSize3, but go on until convergence.
    let [<Literal>] WindowSize3Converge = 12
    /// Like WindowSize4, but go on until convergence.
    let [<Literal>] WindowSize4Converge = 13
    /// Like SiftSymmetric, but can group non-symmetric variables too.
    let [<Literal>] GroupSift = 14
    /// Like GroupSift, but go on until convergence.
    let [<Literal>] GroupSiftConverge = 15
    /// Simulated annealing; potentially very slow!
    let [<Literal>] SimulatedAnnealing = 16
    /// Genetic algorithm; potentially very slow!
    let [<Literal>] GeneticAlgorithm = 17
    /// ZDD only: similar to Sift, but for ZDDs??
    let [<Literal>] LinearSift = 18
    /// ZDD only: Like LinearSift, but go on until convergence.
    let [<Literal>] LinearSiftConverge = 19
    /// ??? Like GroupSift, but ... ummmm ... "lazy", in some way?  No docs here :-/.
    let [<Literal>] LazySift = 20
    /// Dynamic programming for exact reordering.  Very slow by comparison with other methods.
    let [<Literal>] Exact = 21

module Interop =
    [<Literal>]
    let CUDD_LIB =
#if INTERACTIVE
        @"C:\Temp\CUDD3.dll"
#else
        "CUDD3.dll"

    do
        let asm = System.Reflection.Assembly.GetExecutingAssembly()
        asm.GetManifestResourceNames()
        |> Seq.filter (fun x -> x.Contains "CUDD" && (if System.Environment.Is64BitProcess then x.Contains "64" else x.Contains "32"))
        |> Seq.head
        |> (fun x ->
            use stream = asm.GetManifestResourceStream x
            let buf = Array.zeroCreate (int stream.Length)
            ignore <| stream.Read(buf, 0, buf.Length)
            let path = System.IO.Path.Combine(System.IO.Path.GetDirectoryName(asm.Location), CUDD_LIB)
            printfn "Output of %s at: %s" x path
            use output = System.IO.File.Create(path)
            output.Write(buf, 0, buf.Length)
        )
#endif

    open System.Runtime.InteropServices
    [<DllImport(CUDD_LIB)>] // returns a DdManager*
    extern nativeint Cudd_Init(uint32 numVars, uint32 numVarsZ, uint32 numSlots, uint32 cacheSize, uint32 maxMemory)
    [<DllImport(CUDD_LIB)>]
    extern void Cudd_AutodynEnable(nativeint ddManager, int reorderingType)
    [<DllImport(CUDD_LIB)>]
    extern void Cudd_AutodynDisable(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] // returns a DdNode*
    extern nativeint Cudd_bddNewVar(nativeint ddManager)
    [<DllImport(CUDD_LIB)>]
    extern void Cudd_Quit(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_bddAnd(nativeint ddManager, nativeint f, nativeint g)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_bddOr(nativeint ddManager, nativeint f, nativeint g)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_bddXor(nativeint ddManager, nativeint f, nativeint g)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_bddNot(nativeint x)
    [<DllImport(CUDD_LIB)>] /// returns a *DdNode - BDD-specific!
    extern nativeint Cudd_ReadOne(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] /// returns a *DdNode - BDD-specific!
    extern nativeint Cudd_ReadLogicZero(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] /// returns a *DdNode - ZDD-specific!
    extern nativeint Cudd_ReadZddOne(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] /// returns a *DdNode - ZDD-specific!
    extern nativeint Cudd_ReadZero(nativeint ddManager)
    [<DllImport(CUDD_LIB)>] // returns 0 or nonzero
    extern int Cudd_IsConstant(nativeint x)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_T(nativeint x)
    [<DllImport(CUDD_LIB)>] // returns a *DdNode
    extern nativeint Cudd_E(nativeint x)
    [<DllImport(CUDD_LIB)>] // returns a double -- 1 or 0, for a BDD.
    extern double Cudd_V(nativeint x)
    [<DllImport(CUDD_LIB)>] // returns an unsigned integer
    extern uint32 Cudd_NodeReadIndex(nativeint node)
    [<DllImport(CUDD_LIB)>]
    extern void Cudd_Ref(nativeint x)
    [<DllImport(CUDD_LIB)>]
    extern void Cudd_Deref(nativeint x)
    [<DllImport(CUDD_LIB)>]
    extern int Cudd_bddWriteDot(nativeint mgr, int n, nativeint[] roots, string filename, string[] varNames, string[] outNames)
    // Cudd_ReadInvPerm doesn't seem to work - or, more likely, my understanding of it is flawed...
    // So I'm using Cudd_ReadPerm instead, and doing a bit more work on my side.
    [<DllImport(CUDD_LIB)>]
    extern int Cudd_ReadPerm(nativeint mgr, int i)

[<Measure>] type manager
[<Measure>] type node

module BDD =
    open Interop
    [<Literal>]
    let UNIQUE_SLOTS = 256u
    [<Literal>]
    let CACHE_SLOTS = 262144u

    let inline conv (x : nativeint) = int64 x
        //if System.Environment.Is64BitProcess then int64 x
        //else int32 (x &&& 0xffffffffn) |> int64

    let initBDD dwlen sifting : int64<manager> =
        let v = Cudd_Init(dwlen, 0u, UNIQUE_SLOTS, CACHE_SLOTS, 0u)
        if sifting = Reordering.None then Cudd_AutodynDisable(v)
        else Cudd_AutodynEnable(v, sifting)
        conv v * 1L<manager>

    let newVar (mgr : int64<manager>) : int64<node> =
        let v = Cudd_bddNewVar(nativeint mgr)
        conv v * 1L<node>

    let _and (a : int64<node>) (b : int64<node>) (mgr : int64<manager>) : int64<node> =
        let v = Cudd_bddAnd(nativeint mgr, nativeint a, nativeint b)
        conv v * 1L<node>

    let _or (a : int64<node>) (b : int64<node>) (mgr : int64<manager>) : int64<node> =
        let v = Cudd_bddOr(nativeint mgr, nativeint a, nativeint b)
        conv v * 1L<node>

    let _xor (a : int64<node>) (b : int64<node>) (mgr : int64<manager>) : int64<node> =
        let v = Cudd_bddXor(nativeint mgr, nativeint a, nativeint b)
        conv v * 1L<node>

    let _not (x : int64<node>) : int64<node> =
        let v = Cudd_bddNot(nativeint x)
        conv v * 1L<node>

    let _ref (x : int64<node>) = Cudd_Ref(nativeint x)

    let _deref (x : int64<node>) = Cudd_Deref(nativeint x)

    let inline isComplemented (x : int64<node>) : bool = int64 x &&& 1L = 1L

    let constValueOf (x : int64<node>) : bool =
        // see the comment for _zero, to understand how this works!
        let v = Cudd_V(nativeint x)
        assert (v = 1.0) // <- this verifies that /x/ IS a constant!
        let result = int64 x &&& 1L = 0L // if LSB is not set, then it's true.
        result

    let _one (mgr : int64<manager>) : int64<node> =
        let v = Cudd_ReadOne(nativeint mgr)
        assert (constValueOf(conv v * 1L<node>) = true)
        conv v * 1L<node>

    let _zero (mgr : int64<manager>) : int64<node> =
        // now, LOGIC zero for a BDD is the CUDD complement of Cudd_ReadOne(...).
        // That means that the internal constant value is ALWAYS 1.0, whether
        // we're talking about BDD 0 or BDD 1.
        // However, a 1 is indicated by the fact that the pointer's LSB is complemented.
        let v = Cudd_ReadLogicZero(nativeint mgr)
        assert (constValueOf(conv v * 1L<node>) = false)
        conv v * 1L<node>

    let close (mgr : int64<manager>) = Cudd_Quit(nativeint mgr)

    let isConstant (x : int64<node>) : bool =
        Cudd_IsConstant(nativeint x) <> 0

    let thenChild (x : int64<node>) : int64<node> =
        let v = Cudd_T(nativeint x)
        conv v * 1L<node>

    let elseChild (x : int64<node>) : int64<node> =
        let v = Cudd_E(nativeint x)
        conv v * 1L<node>

    let readIndexOf (x : int64<node>) : int = Cudd_NodeReadIndex(nativeint x) |> int

    let readPerm (x : int64<manager>) (i : int) : int = Cudd_ReadPerm(nativeint x, i) 

    let writeDotFile fn varNames outNames (mgr : int64<manager>) (roots : int64<node>[]) : bool =
        let roots = Array.map nativeint roots
        let n = roots.Length
        //Cudd_bddWriteDot(nativeint mgr, n, roots, fn, varNames, outNames) = 1
        Cudd_bddWriteDot(nativeint mgr, n, roots, fn, varNames, outNames) = 1

open FinalEquation.CommonStructure

type BDDReorderingStats = {
    Method : int
    AndTimesMS : float[]
    OrTimesMS : float[]
    XorTimesMS : float[]
    NodeOrdering : uint32[]
}

type NodeType =
| One
| Zero
| Opaque of int64<node>

and Node(root) =
    member __.Value
        with get () =
            if BDD.isConstant root then
                if BDD.constValueOf root then One
                else Zero
            else
                Opaque root
    member __.ThenChild with get () = Node(BDD.thenChild root)
    member __.ElseChild with get () = Node(BDD.elseChild root)
    member __.IsComplemented with get () = BDD.isComplemented root

type BinaryDecisionDiagram (dwlen : uint32, ?reordering) as __ =
    let mutable print_count_after_ops = false
    let reordering = defaultArg reordering Reordering.None
    let mgr = BDD.initBDD dwlen reordering
    let bddNodes = System.Collections.Generic.List()
    /// Maps cudd_idx to var_idx
    let varMap = System.Collections.Generic.Dictionary<int,uint32>()
    /// Maps var_idx to cudd_idx
    let invVarMap = System.Collections.Generic.Dictionary<uint32,int>()
    let times_and = System.Collections.Generic.List()
    let times_or = System.Collections.Generic.List()
    let times_xor = System.Collections.Generic.List()
    let time (coll : System.Collections.Generic.List<_>) =
        let sw = System.Diagnostics.Stopwatch()
        fun f ->
            sw.Restart ()
            let v = f ()
            sw.Stop()
            coll.Add sw.Elapsed.TotalMilliseconds
            v
    let keep x =
        BDD._ref x
        if print_count_after_ops then printfn "NodeCount %d" (__.NodeCount [x])
        bddNodes.Add x; x

    member __.ReorderStats =
        {
            Method = reordering
            AndTimesMS = times_and.ToArray ()
            OrTimesMS = times_or.ToArray ()
            XorTimesMS = times_xor.ToArray ()
            NodeOrdering = [|0..int dwlen-1|] |> Array.sortBy (BDD.readPerm mgr) |> Array.map uint32
        }

    member __.WriteDot fn outputs =
        // each root has got a particular index; and each index is associated with a particular variable name.
        let out_names, roots = Array.unzip outputs
        let maxIdx = varMap.Keys |> Seq.max
        let node_names = Array.zeroCreate (int maxIdx+1)
        for n = 0 to int dwlen-1 do
            if invVarMap.ContainsKey (uint32 n) then
                let cudd_idx = invVarMap.[uint32 n]
                node_names.[cudd_idx] <- sprintf "bit-%d" n
        BDD.writeDotFile fn node_names out_names mgr roots

    member __.Nodeify root = Node(root)

    member __.NodeCount (roots : seq<int64<node>>) =
        let seenList = System.Collections.Generic.HashSet()
        let rec count n cur =
            if BDD.isConstant cur || seenList.Contains cur then 0
            else
                seenList.Add cur |> ignore
                1 + count n (BDD.thenChild cur) + count n (BDD.elseChild cur)
        roots |> Seq.sumBy (count 0)

    member __.PrintCountAfterOps with get () = print_count_after_ops and set v = print_count_after_ops <- v

    interface IRepresentation< int64<node> > with
        member __.Constants = {One=BDD._one mgr; Zero=BDD._zero mgr}
        member __.And a b = time times_and (fun () -> BDD._and a b mgr) |> keep
        member __.Or a b = time times_or (fun () -> BDD._or a b mgr) |> keep
        member __.Xor a b = time times_xor (fun () -> BDD._xor a b mgr) |> keep
        member __.Not x = BDD._not x // this is just a complement, not a new node.
        member __.MakeVariable n =
            let v = BDD.newVar mgr
            let cudd_idx = BDD.readIndexOf v
            varMap.[cudd_idx] <- n
            invVarMap.[n] <- cudd_idx
            v
        (*
           Evaluation is interesting.  CUDD has the notion of an *index*, which seems to be synonymous
           with the order/level of a particular variable in the tree.  During BDD creation, it can re-order the
           nodes (and it SHOULD reorder them to avoid horrible space&time explosions); but the indices
           remain the same.   Because of how a BDD is structured, a reordering of one node must reorder
           all nodes that are at the same level.
           
           Now, from MakeVariable, I get a BDD that represents a single variable; I'll call this my /origNode/.
           In MakeVariable, I am also passed the word-bit that /origNode/ is supposed to represent.  So I can
           make a mapping: /origNode/ => /Var/.  I can also read the index of /origNode/ when it is
           created, and make a mapping: /index/ => /Var/.

           Some operations occur, and let's assume that sifting has changed some things around.  Now, I
           get a "root" (i.e. the /point/ in Evaluate) and I want to find out which branch of the /root/ to
           follow; so, I need to look at the data.  But which data bit?  Given a /root/, I need to find the /Var/.
           I can look up the /index/ of the /root/, and then it's a simple lookup away.
        *)
        member __.Evaluate data point =
            let rec evaluate node =
                if BDD.isConstant node then
                    BDD.constValueOf node
                else
                    let cudd_idx = BDD.readIndexOf node
                    //printfn "cudd_idx is %d, looking for that in map..." cudd_idx
                    let my_idx = int varMap.[cudd_idx]
                    if data.[my_idx/32].[my_idx%32] then
                        if BDD.isComplemented node then not (evaluate (BDD.thenChild node))
                        else evaluate (BDD.thenChild node)
                    else
                        if BDD.isComplemented node then not (evaluate (BDD.elseChild node))
                        else evaluate (BDD.elseChild node)
            evaluate point
        member __.EvaluationCache data = None
        member __.IsZero x = BDD.isConstant x && BDD.constValueOf x = false
        member __.IsOne x = BDD.isConstant x && BDD.constValueOf x = true
        member __.Dispose () =
            for x in bddNodes do BDD._deref x
            BDD.close mgr
