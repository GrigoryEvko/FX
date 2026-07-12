import FX1Poly.Polygraph.Homology.FiniteCarrierWalkPigeonhole

/-! # FX1Poly/Polygraph/Homology/NaryAlphabetObstructionChainEnumerator — the n-ary alphabet
    obstruction-chain enumerator that SUBSUMES the binary one, the n-ary censuses (complete graph,
    disjoint union), and the reconnection of the r11 hostile graphs now seen at their true alphabet
    (TOWER-ANICK r12, #2144)

The r11 file `FiniteCarrierWalkPigeonhole` shipped the classical finite-carrier walk pigeonhole
`listOverCarrierRepeats` (ingredient (i) of the general-graph acyclicity-soundness node) and, while
truth-probing three hostile graphs, surfaced FINDING A — **the alphabet wall**: the shipped
`allWordsOfLength` / `multiObstructionChainRankOracle` enumerate only BINARY words (`0 :: _` / `1 :: _`),
so the census is BLIND to any letter `>= 2`.  Both the DAG chain and the diamond, though they live on
`>= 3` letters, produced the SAME census as `{xy}` — an artifact, not the truth.  r11 therefore recorded
a NEW prerequisite absent from r10's three-ingredient list, residual (0) of
`generalGraphSoundnessResidualsAfterPigeonhole`: an n-ary alphabet enumerator + a re-based census oracle.
The general node has FOUR ingredients, not three.  **This module ships residual (0).**

## What this module delivers (additive-only; the binary file stays verbatim UNMOVED)

  * `allWordsOverAlphabet` — ★ THE ONE NEW DEFINITION: all words of a given length over an ARBITRARY
    `List Nat` alphabet, hand-rolled structural `flatMap` + `map` (the generator
    `fun word => alphabet.map (fun letter => letter :: word)` reads the alphabet as data, no `{0, 1}`
    baked in).  `multiObstructionChainsAtDegreeOver` / `multiObstructionChainRankOracleOver` re-base the
    r3 filter / rank pipeline on it — the GUARD (`allAdjacentPairsAreObstructions`) is reused verbatim
    (it already reads arbitrary `Nat` letters), so the n-ary port is a ONE-definition pivot.
  * The n-ary length bridge (four zero-axiom lemmas, the genuinely-new proof burden): `memAppendCases`
    (a hand-rolled append-splitter — the variable-arity `map` forces an honest `++` split where r10's
    binary generator dodged it via concrete cons-reduction), `memMapConsHasLength`,
    `memFlatMapWordsOverAlphabetHasLength`, and `memWordsOverAlphabetHasLength` — `word ∈
    allWordsOverAlphabet alphabet n ==> word.length = n`, the n-ary analog of r10's crossed wall, all via
    the `List.Mem`-constructor route (never `List.mem_append` / `List.mem_map`, both leak `propext`).
  * ★★ **THE SUBSUMPTION HEADLINE**: `binaryEnumeratorAgrees` (`allWordsOverAlphabet [0, 1] n =
    allWordsOfLength n`, `rw` + explicit `rfl`) and `binaryOracleAgrees`
    (`multiObstructionChainRankOracleOver [0, 1] obs d = multiObstructionChainRankOracle obs d`).  The
    n-ary oracle SUBSUMES the shipped binary one, so every r3/r5/r6/r10 binary census is recovered by
    specialization at `[0, 1]` — no regression, the old file UNMOVED.
  * The n-ary censuses (all truth-probed by an independent enumeration BEFORE proving, then `rfl` on the
    computed values): `naryCompleteGraphCensus` (`3, 9, 27, 81, 243` over `{2, 3, 4}` — the n-ary
    exponential, alphabet size the base), `naryDisjointUnionCensus` (the three-block union
    `{xx} + {yy} + {zz}` over `[0, 1, 2]`: union `3, 3, 3, 3, 3`, each block `3, 1, 1, 1, 1`) with the
    LITERAL list split `chains_union 2 = chains_xx 2 ++ chains_yy 2 ++ chains_zz 2` and rank additivity
    `3 = 1 + 1 + 1` at degree `>= 1` (degree 0 EXCLUDED — the fixed-alphabet double-count `3 != 9`), and
    `binaryRegressionCensus` (`[0, 1]` reproduces Fibonacci `2, 3, 5, 8, 13, 21` and `{xy}`
    `2, 1, 0, 0, 0`).
  * The reconnection corollaries — the r11 hostile graphs healed, now seen at their TRUE alphabet:
    `dagChainNaryCensus` (`4, 3, 2, 1` then `0` at degree 4, over `[0, 1, 2, 3]`), `diamondNaryCensus`
    (`4, 4, 2, 0`), each truncating at their real longest-path degree instead of the r11 blind `0`, and
    `threeCycleNaryCensusIsConstant` (`3, 3, 3, 3, 3, 3` — cyclic, NEVER truncates, the honest converse).
    Plus the n-ary census -> exactness bridge `censusZeroImpliesExactOver` (mirrors r6's
    `censusZeroImpliesExact`, same `⟨[[0]]⟩` zero boundary, no Smith surgery) with truncation witnesses.

## Honest scope (NO overclaim — the standing walls stay NAMED)

r12 delivers residual (0) of the r11 pigeonhole node ONLY.  It does NOT close:

  * residual (ii) **checker saturation** (a length-`L` cycle is caught only at `fuel >= L - 1`);
  * residual (iii) **the topological-sort longest-path bound** (an acyclic graph's valid walk has no
    repeated vertex, so chains die above `vertexCount`);
  * the final assembly wiring (0)+(i)+(ii)+(iii) into the general census-zero closed form;
  * `naryDisjointAdditivityGeneralIsNamedNode` — the GENERAL `∀ degree >= 1` list-split / rank additivity
    for a `k`-block disjoint union (the concrete 3-block seed ships; the `∀`-degree statement resists
    induction identically to r10's `disjointUnionAdditivityIsNamedNode`).

With residual (0) SHIPPED, `generalGraphSoundnessResidualsAfterPigeonhole` flips its (0) marker in its
own docstring (the honest-record convention, `Bool := true` unchanged); the general node stays named on
(ii)+(iii)+assembly.  No Smith import, no lane-law violation, no Homology<->Omega edge.

## Zero-axiom design decisions (the lane's propext minefield)

  * Membership is BUILT and DESTRUCTURED by `List.Mem.head` / `List.Mem.tail` constructors — never
    `decide` on `List.Mem` (leaks `propext`), never `List.mem_append` / `List.mem_map` (both leak).  The
    variable-arity `flatMap`-cons `(base :: rest).flatMap gen = gen base ++ rest.flatMap gen` is split by
    the hand-rolled `memAppendCases` (structural on the left list) rather than r10's fixed cons chain.
  * `binaryEnumeratorAgrees` unfolds one `flatMap` step by `show`, `rw`s the induction hypothesis, then
    closes with an EXPLICIT `rfl` (default transparency reduces `[0, 1].map (fun letter => letter :: word)`
    to `[0 :: word, 1 :: word]`; the `rw` trailing reducible-only `rfl` does not — the r10 `sorryAx`
    trap).  `binaryOracleAgrees` is `congrArg List.length` of the chain-list agreement.
  * The census list splits / additivity are `rfl` on the COMPUTED lists — never `==` / `DecidableEq` on
    `List (List Nat)` (`List.append_nil` / `List.length_append` leak `propext`).
  * The compute-heavy censuses (candidate spaces up to `4^5`) carry a scoped `set_option maxRecDepth`
    (an elaboration stack limit, axiom-neutral — the kernel still checks every `rfl`).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (length `Nat` / alphabet / word lists).  Per-declaration gated (and independently `#print
axioms`-checked for the four load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/NaryAlphabetObstructionChainEnumerator.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

-- The compute-heavy censuses in sections D/E/F reduce candidate spaces up to `4^5`; the raised
-- `maxRecDepth` is an elaboration stack limit only (axiom-neutral — the kernel still checks every
-- `rfl`).  The structural bridge lemmas in sections A/B/C do not depend on it.
set_option maxRecDepth 8000

/-! ## A — the n-ary alphabet enumerator (the ONE new def) + the re-based census pipeline -/

/-- ★ **THE n-ary ALPHABET ENUMERATOR.**  All words of a given length over an ARBITRARY `List Nat`
alphabet, hand-rolled structural `flatMap` + `map`.  The generator `fun word => alphabet.map (fun letter
=> letter :: word)` reads the alphabet as DATA — no `{0, 1}` baked in (FINDING A's wall crossed).  At
`[0, 1]` it reduces to the shipped `allWordsOfLength` (`binaryEnumeratorAgrees`). -/
def allWordsOverAlphabet (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      (allWordsOverAlphabet alphabet length).flatMap
        (fun word => alphabet.map (fun letter => letter :: word))

/-- ★ **THE n-ary MULTI-OBSTRUCTION ENUMERATOR.**  The minimal chains at a degree = all words of length
`degree + 1` over the alphabet filtered by the (verbatim-reused) decidable guard.  Only the candidate
space is new; the guard `allAdjacentPairsAreObstructions` already reads arbitrary `Nat` letters. -/
def multiObstructionChainsAtDegreeOver (alphabet : List Nat) (obstructions : List (Nat × Nat))
    (degree : Nat) : List (List Nat) :=
  (allWordsOverAlphabet alphabet (degree + 1)).filter (allAdjacentPairsAreObstructions obstructions)

/-- ★ **THE n-ary RANK ORACLE.**  The per-degree chain count over an arbitrary alphabet — the same
`Nat`-valued interface as r3's `multiObstructionChainRankOracle`, now able to SEE letters `>= 2`. -/
def multiObstructionChainRankOracleOver (alphabet : List Nat) (obstructions : List (Nat × Nat))
    (degree : Nat) : Nat :=
  (multiObstructionChainsAtDegreeOver alphabet obstructions degree).length

/-! ## B — the n-ary length bridge (four zero-axiom lemmas via the `List.Mem`-constructor route) -/

/-- **The append-splitter**: a member of `first ++ second` is a member of `first` or of `second`.  NEW
for r12 — r10's binary generator dodged `++` via concrete cons-reduction, but the variable-arity `map`
forces an honest split.  Structural on `first`; the `List.Mem` witness is destructured through its
constructors (never `List.mem_append`, which leaks `propext`). -/
theorem memAppendCases {carrier : Type} (second : List carrier) (element : carrier) :
    ∀ (first : List carrier), element ∈ first ++ second → element ∈ first ∨ element ∈ second
  | [], hMem => Or.inr hMem
  | head :: remainingFirst, hMem => by
      have hMemCons : element ∈ head :: (remainingFirst ++ second) := hMem
      cases hMemCons with
      | head => exact Or.inl (List.Mem.head remainingFirst)
      | tail _ hMemTail =>
          cases memAppendCases second element remainingFirst hMemTail with
          | inl hInFirst => exact Or.inl (List.Mem.tail head hInFirst)
          | inr hInSecond => exact Or.inr hInSecond

/-- **The map-cons leaf**: every word of `alphabet.map (fun letter => letter :: base)` has length
`base.length + 1` (each cons prepends one letter).  Structural on the alphabet; the `List.Mem` witness is
destructured by its constructors (never `List.mem_map`, which leaks `propext`).  The head arm closes by
`congrArg (· + 1)` of the base-length hypothesis. -/
theorem memMapConsHasLength (base : List Nat) (length : Nat) (hBaseLen : base.length = length) :
    ∀ (alphabet : List Nat) (resultWord : List Nat),
      resultWord ∈ alphabet.map (fun letter => letter :: base) →
      resultWord.length = length + 1
  | [], resultWord, hMem => by
      have hMemNil : resultWord ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | alphabetHead :: remainingAlphabet, resultWord, hMem => by
      have hMemCons : resultWord ∈
          (alphabetHead :: base) :: remainingAlphabet.map (fun letter => letter :: base) := hMem
      cases hMemCons with
      | head => exact congrArg (fun measured => measured + 1) hBaseLen
      | tail _ hMemTail =>
          exact memMapConsHasLength base length hBaseLen remainingAlphabet resultWord hMemTail

/-- **The inner list-induction of the n-ary length bridge**: if every base word of `wordsList` has
length `length`, then every word of the `flatMap` (one alphabet letter prepended per base) has length
`length + 1`.  Structural on `wordsList`; the `flatMap`-cons reduces DEFINITIONALLY to `gen base ++
remainingBases.flatMap gen`, split by `memAppendCases`, and the map arm delegated to
`memMapConsHasLength`.  Never `List.mem_flatMap` / `List.mem_append` (both leak `propext`). -/
theorem memFlatMapWordsOverAlphabetHasLength (alphabet : List Nat) (length : Nat) :
    ∀ (wordsList : List (List Nat)),
      (∀ base, base ∈ wordsList → base.length = length) →
      ∀ resultWord,
        resultWord ∈ wordsList.flatMap (fun word => alphabet.map (fun letter => letter :: word)) →
        resultWord.length = length + 1
  | [], _, _, hMem => by
      have hMemNil : _ ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | base :: remainingBases, hAllBaseLen, resultWord, hMem => by
      have hBaseLen : base.length = length := hAllBaseLen base (List.Mem.head remainingBases)
      have hMemAppend : resultWord ∈
          alphabet.map (fun letter => letter :: base)
            ++ remainingBases.flatMap (fun word => alphabet.map (fun letter => letter :: word)) := hMem
      cases memAppendCases _ resultWord _ hMemAppend with
      | inl hInMap =>
          exact memMapConsHasLength base length hBaseLen alphabet resultWord hInMap
      | inr hInRest =>
          exact memFlatMapWordsOverAlphabetHasLength alphabet length remainingBases
            (fun candidate hCandidate => hAllBaseLen candidate (List.Mem.tail base hCandidate))
            resultWord hInRest

/-- ★★ **THE n-ary CROSSED WALL**: `word ∈ allWordsOverAlphabet alphabet targetLength ==>
word.length = targetLength`.  Outer STRUCTURAL induction on `targetLength` (`0 => [[]]`, the singleton
`[]`; `n + 1 => flatMap`, delegated to `memFlatMapWordsOverAlphabetHasLength`).  The n-ary analog of
r10's `memWordsHasLength`, now over an arbitrary alphabet — the load-bearing length fact the general
pigeonhole application needs. -/
theorem memWordsOverAlphabetHasLength (alphabet : List Nat) :
    ∀ (targetLength : Nat) (word : List Nat),
      word ∈ allWordsOverAlphabet alphabet targetLength → word.length = targetLength
  | 0, word, hMem => by
      have hMemSingleton : word ∈ ([[]] : List (List Nat)) := hMem
      cases hMemSingleton with
      | head => rfl
      | tail _ hMemTail => cases hMemTail
  | targetLength + 1, word, hMem =>
      memFlatMapWordsOverAlphabetHasLength alphabet targetLength
        (allWordsOverAlphabet alphabet targetLength)
        (fun base hBase => memWordsOverAlphabetHasLength alphabet targetLength base hBase) word hMem

/-! ## C — the SUBSUMPTION headline: the n-ary oracle recovers the shipped binary one -/

/-- ★★ **THE SUBSUMPTION**: `allWordsOverAlphabet [0, 1] n = allWordsOfLength n`.  Structural on `n`; the
`n + 1` step unfolds one `flatMap` by `show`, rewrites the induction hypothesis, and closes with an
EXPLICIT `rfl` (default transparency reduces `[0, 1].map (fun letter => letter :: word)` to
`[0 :: word, 1 :: word]`, matching the shipped generator — the `rw` trailing reducible `rfl` does not
unfold `List.map`). -/
theorem binaryEnumeratorAgrees : ∀ n, allWordsOverAlphabet [0, 1] n = allWordsOfLength n
  | 0 => rfl
  | n + 1 => by
      show (allWordsOverAlphabet [0, 1] n).flatMap
              (fun word => [0, 1].map (fun letter => letter :: word))
          = (allWordsOfLength n).flatMap (fun word => [0 :: word, 1 :: word])
      rw [binaryEnumeratorAgrees n]
      exact rfl

/-- **The n-ary chain list = the binary chain list at `[0, 1]`**: the guard-filtered candidate lists
coincide once the enumerators do (`binaryEnumeratorAgrees`). -/
theorem binaryChainsAgree (obstructions : List (Nat × Nat)) (degree : Nat) :
    multiObstructionChainsAtDegreeOver [0, 1] obstructions degree
      = multiObstructionChainsAtDegree obstructions degree := by
  show (allWordsOverAlphabet [0, 1] (degree + 1)).filter
          (allAdjacentPairsAreObstructions obstructions)
      = (allWordsOfLength (degree + 1)).filter (allAdjacentPairsAreObstructions obstructions)
  rw [binaryEnumeratorAgrees (degree + 1)]

/-- ★★ **THE n-ary ORACLE SUBSUMES THE BINARY ONE**: `multiObstructionChainRankOracleOver [0, 1] obs d =
multiObstructionChainRankOracle obs d` for EVERY obstruction system and degree.  `congrArg List.length`
of the chain-list agreement — so every shipped binary census (Fibonacci, `{xy}`, the disjoint blocks)
is the `[0, 1]` specialization of the n-ary oracle.  No regression; the r3 file stays UNMOVED. -/
theorem binaryOracleAgrees (obstructions : List (Nat × Nat)) (degree : Nat) :
    multiObstructionChainRankOracleOver [0, 1] obstructions degree
      = multiObstructionChainRankOracle obstructions degree :=
  congrArg List.length (binaryChainsAgree obstructions degree)

/-! ## D — the n-ary censuses (truth-probed by an independent enumeration BEFORE proving) -/

/-- The complete graph on `{2, 3, 4}` — all nine edges `(2, 2) … (4, 4)`, so EVERY word over `{2, 3, 4}`
passes the guard. -/
def completeGraphObstructions : List (Nat × Nat) :=
  [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)]

/-- The three-letter alphabet `{2, 3, 4}` for the complete-graph census. -/
def completeGraphAlphabet : List Nat := [2, 3, 4]

/-- ★★ **THE n-ary EXPONENTIAL CENSUS**: `c(0..4) = 3, 9, 27, 81, 243 = 3^(d+1)` for the complete graph
on `{2, 3, 4}` — the n-ary analog of the binary complete graph's `2^(d+1)`, with the ALPHABET SIZE as
the exponential base.  The binary oracle returns `0` here for all degrees (FINDING A's blindness); the
n-ary oracle sees the true count.  `rfl` on `Nat` literals (a compute-heavy `4^5`-scale reduction —
scoped `maxRecDepth`). -/
theorem naryCompleteGraphCensus :
    multiObstructionChainRankOracleOver completeGraphAlphabet completeGraphObstructions 0 = 3 ∧
    multiObstructionChainRankOracleOver completeGraphAlphabet completeGraphObstructions 1 = 9 ∧
    multiObstructionChainRankOracleOver completeGraphAlphabet completeGraphObstructions 2 = 27 ∧
    multiObstructionChainRankOracleOver completeGraphAlphabet completeGraphObstructions 3 = 81 ∧
    multiObstructionChainRankOracleOver completeGraphAlphabet completeGraphObstructions 4 = 243 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The disjoint-union alphabet `[0, 1, 2]` (three letter-disjoint self-loop blocks). -/
def disjointUnionAlphabet : List Nat := [0, 1, 2]

/-- The `{xx}` disjoint block `[(0, 0)]` (self-loop on letter `0`). -/
def disjointBlockXx : List (Nat × Nat) := [(0, 0)]

/-- The `{yy}` disjoint block `[(1, 1)]` (self-loop on letter `1`). -/
def disjointBlockYy : List (Nat × Nat) := [(1, 1)]

/-- The `{zz}` disjoint block `[(2, 2)]` (self-loop on letter `2`). -/
def disjointBlockZz : List (Nat × Nat) := [(2, 2)]

/-- The disjoint UNION `{xx, yy, zz} = [(0, 0), (1, 1), (2, 2)]` — three self-loops on DISJOINT letters,
so its chains are monochromatic (a cross-letter pair is not an obstruction). -/
def disjointUnionSystem : List (Nat × Nat) := [(0, 0), (1, 1), (2, 2)]

/-- ★ **THE THREE-BLOCK DISJOINT-UNION CENSUS** (`rfl` on `Nat` literals): over `[0, 1, 2]` the union
counts `3, 3, 3, 3, 3` (three monochromatic chains at each degree `>= 1`; degree 0 = the three length-1
words), and each block `{xx}` / `{yy}` / `{zz}` counts `1` at degree 2 (its single monochromatic chain).
The n-ary lift of r10's two-block `{xx} + {yy}` seed. -/
theorem naryDisjointUnionCensus :
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 0 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 1 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 2 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 3 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 4 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockXx 2 = 1 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockYy 2 = 1 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockZz 2 = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **THE DISJOINT-UNION MAYER-VIETORIS SEED (n-ary, three blocks)**: the union chains split as a
LITERAL list concatenation `chains_union 2 = chains_xx 2 ++ chains_yy 2 ++ chains_zz 2` (the union chain
list `[[0, 0, 0], [1, 1, 1], [2, 2, 2]]` is exactly the three monochromatic singletons concatenated — no
cross terms), and the ranks ADD `rank_union 3 = rank_xx 3 + rank_yy 3 + rank_zz 3` (`3 = 1 + 1 + 1`).
Both `rfl` on the COMPUTED lists (never `==` on `List (List Nat)`).  Degree `>= 1` only. -/
theorem naryDisjointUnionListSplitAndAdditivity :
    multiObstructionChainsAtDegreeOver disjointUnionAlphabet disjointUnionSystem 2
      = multiObstructionChainsAtDegreeOver disjointUnionAlphabet disjointBlockXx 2
          ++ multiObstructionChainsAtDegreeOver disjointUnionAlphabet disjointBlockYy 2
          ++ multiObstructionChainsAtDegreeOver disjointUnionAlphabet disjointBlockZz 2 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 3
      = multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockXx 3
          + multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockYy 3
          + multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockZz 3 :=
  ⟨rfl, rfl⟩

/-- ★ **DEGREE 0 EXCLUDED (honest artifact)**: at degree 0 the union counts `3` but the blocks sum to
`9` (`3 != 3 + 3 + 3`) — the fixed-alphabet length-1 double-count flagged lane-wide.  Additivity holds
only for degree `>= 1`.  `rfl`. -/
theorem naryDisjointUnionDegreeZeroExcluded :
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointUnionSystem 0 = 3 ∧
    multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockXx 0
        + multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockYy 0
        + multiObstructionChainRankOracleOver disjointUnionAlphabet disjointBlockZz 0 = 9 :=
  ⟨rfl, rfl⟩

/-- ★ **THE BINARY REGRESSION** (subsumption cross-check, `rfl` on `Nat` literals): at `[0, 1]` the
n-ary oracle reproduces the shipped Fibonacci census `2, 3, 5, 8, 13, 21` (the branching
`fibObstructionSystem`) and the `{xy}` truncating census `2, 1, 0, 0, 0` (`linearObstructionSystem`) —
computed directly through the n-ary enumerator, confirming `binaryOracleAgrees` on the two headline
systems. -/
theorem binaryRegressionCensus :
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 0 = 2 ∧
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 1 = 3 ∧
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 2 = 5 ∧
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 3 = 8 ∧
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 4 = 13 ∧
    multiObstructionChainRankOracleOver [0, 1] fibObstructionSystem 5 = 21 ∧
    multiObstructionChainRankOracleOver [0, 1] linearObstructionSystem 0 = 2 ∧
    multiObstructionChainRankOracleOver [0, 1] linearObstructionSystem 1 = 1 ∧
    multiObstructionChainRankOracleOver [0, 1] linearObstructionSystem 2 = 0 ∧
    multiObstructionChainRankOracleOver [0, 1] linearObstructionSystem 3 = 0 ∧
    multiObstructionChainRankOracleOver [0, 1] linearObstructionSystem 4 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## E — the reconnection corollaries (the r11 hostile graphs, now seen at their TRUE alphabet) -/

/-- The four-letter alphabet `[0, 1, 2, 3]` on which the r11 DAG chain and diamond genuinely live. -/
def graphReconnectAlphabet : List Nat := [0, 1, 2, 3]

/-- The DAG chain `[(0, 1), (1, 2), (2, 3)]` — the r11 hostile graph whose BINARY census was blind `0`
at degree 2 (`dagChainIsAcyclicWithVanishingBinaryCensus`). -/
def dagChainSystem : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3)]

/-- The diamond `[(0, 1), (0, 2), (1, 3), (2, 3)]` — the r11 hostile graph, likewise binary-blind. -/
def diamondSystem : List (Nat × Nat) := [(0, 1), (0, 2), (1, 3), (2, 3)]

/-- The three-letter alphabet `[0, 1, 2]` for the directed 3-cycle. -/
def threeCycleAlphabet : List Nat := [0, 1, 2]

/-- The directed 3-cycle `[(0, 1), (1, 2), (2, 0)]` — CYCLIC, so its census never truncates. -/
def threeCycleSystem : List (Nat × Nat) := [(0, 1), (1, 2), (2, 0)]

/-- ★★ **THE DAG CHAIN HEALED**: over `[0, 1, 2, 3]` the DAG chain's true census is `4, 3, 2, 1`
(degrees 0..3), truncating at its longest path (`0 -> 1 -> 2 -> 3`, degree 3).  Where r11's BINARY
oracle saw a blind `0` at degree 2, the n-ary oracle sees the real decay.  `rfl` (scoped
`maxRecDepth`). -/
theorem dagChainNaryCensus :
    multiObstructionChainRankOracleOver graphReconnectAlphabet dagChainSystem 0 = 4 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet dagChainSystem 1 = 3 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet dagChainSystem 2 = 2 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet dagChainSystem 3 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **THE DAG CHAIN TRUNCATES**: census `0` at degree 4 (above the longest path).  `rfl` over the
`4^5` candidate space (scoped `maxRecDepth`). -/
theorem dagChainNaryCensusZeroAtDegreeFour :
    multiObstructionChainRankOracleOver graphReconnectAlphabet dagChainSystem 4 = 0 := rfl

/-- ★★ **THE DIAMOND HEALED**: over `[0, 1, 2, 3]` the diamond's true census is `4, 4, 2, 0` (degrees
0..3), truncating at degree 3 (its two length-3 paths `0 -> 1 -> 3`, `0 -> 2 -> 3` are the top chains at
degree 2).  `rfl` (scoped `maxRecDepth`). -/
theorem diamondNaryCensus :
    multiObstructionChainRankOracleOver graphReconnectAlphabet diamondSystem 0 = 4 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet diamondSystem 1 = 4 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet diamondSystem 2 = 2 ∧
    multiObstructionChainRankOracleOver graphReconnectAlphabet diamondSystem 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★★ **THE 3-CYCLE IS CONSTANT (the honest converse)**: over `[0, 1, 2]` the directed 3-cycle's census
is `3, 3, 3, 3, 3, 3` — it NEVER truncates (the cyclic graph admits arbitrarily long chains, three per
degree, one per rotation).  Exactly the graph r11 reported non-acyclic; here the census confirms
non-truncation.  `rfl` over the `3^6` candidate space (scoped `maxRecDepth`). -/
theorem threeCycleNaryCensusIsConstant :
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 0 = 3 ∧
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 1 = 3 ∧
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 2 = 3 ∧
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 3 = 3 ∧
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 4 = 3 ∧
    multiObstructionChainRankOracleOver threeCycleAlphabet threeCycleSystem 5 = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## F — the n-ary census -> exactness bridge (mirrors r6, no Smith surgery) -/

/-- The homology data at a degree of the n-ary tensored complex: the n-ary census rank with zero
boundary matrices (`[[0]]`).  Mirrors r6's `multiObstructionHomologyDataAtDegree` verbatim, re-based on
the n-ary oracle; no new `SmithHomologyData` fields, no direct Smith import. -/
def multiObstructionHomologyDataAtDegreeOver (alphabet : List Nat) (obstructions : List (Nat × Nat))
    (degree : Nat) : SmithHomologyData :=
  { chainBasisCount := multiObstructionChainRankOracleOver alphabet obstructions degree
  , smithBoundaryIntoLower := ⟨[[0]]⟩
  , windowIntoLower := 1
  , smithBoundaryFromHigher := ⟨[[0]]⟩
  , windowFromHigher := 1 }

/-- The homology invariant of the zero-boundary n-ary data is free on the census: `⟨census, []⟩`.  The
two `smithRankWithin [[0]] 1` reduce to `0` and the within-window invariant factors to `[]`.  `rfl`. -/
theorem multiObstructionHomologyInvariantIsFreeOnCensusOver (alphabet : List Nat)
    (obstructions : List (Nat × Nat)) (degree : Nat) :
    (multiObstructionHomologyDataAtDegreeOver alphabet obstructions degree).homologyInvariant
      = ⟨multiObstructionChainRankOracleOver alphabet obstructions degree, []⟩ := rfl

/-- ★★ **THE n-ary CONDITIONAL VANISHING**: an n-ary degree with no chains contributes trivial homology
— `multiObstructionChainRankOracleOver alphabet obs degree = 0 ==> isExactAtDegree
(multiObstructionHomologyDataAtDegreeOver alphabet obs degree)`.  The `rfl` bridge gives `⟨census, []⟩`;
`congrArg` of the census-zero hypothesis collapses the free rank to `0`.  Mirrors r6's
`censusZeroImpliesExact`; bridges ANY truncating n-ary census to exactness. -/
theorem censusZeroImpliesExactOver (alphabet : List Nat) (obstructions : List (Nat × Nat))
    (degree : Nat)
    (censusIsZero : multiObstructionChainRankOracleOver alphabet obstructions degree = 0) :
    isExactAtDegree (multiObstructionHomologyDataAtDegreeOver alphabet obstructions degree) :=
  (multiObstructionHomologyInvariantIsFreeOnCensusOver alphabet obstructions degree).trans
    (congrArg (fun freeRankValue => (⟨freeRankValue, []⟩ : HomologyInvariant)) censusIsZero)

/-- ★ **THE DAG CHAIN IS EXACT ABOVE ITS LONGEST PATH**: `isExactAtDegree` at degree 4, off the
truncation `dagChainNaryCensusZeroAtDegreeFour` — the healed reconnection delivering genuine exactness
where r11 could only report a blind binary `0`. -/
theorem dagChainExactAtDegreeFour :
    isExactAtDegree (multiObstructionHomologyDataAtDegreeOver graphReconnectAlphabet dagChainSystem 4) :=
  censusZeroImpliesExactOver graphReconnectAlphabet dagChainSystem 4 dagChainNaryCensusZeroAtDegreeFour

/-- ★ **THE DIAMOND IS EXACT AT ITS TRUNCATION**: `isExactAtDegree` at degree 3, off the diamond census
(`diamondNaryCensus`'s degree-3 zero). -/
theorem diamondExactAtDegreeThree :
    isExactAtDegree (multiObstructionHomologyDataAtDegreeOver graphReconnectAlphabet diamondSystem 3) :=
  censusZeroImpliesExactOver graphReconnectAlphabet diamondSystem 3 rfl

/-! ## G — the standing walls (NAMED) and the r12 ledger -/

/-- ★ **The general `∀ degree >= 1` k-block disjoint-union additivity is a NAMED node.**  The concrete
three-block witnesses are SHIPPED (`naryDisjointUnionListSplitAndAdditivity`: the degree-2 list split +
the degree-3 rank additivity, both `rfl`).  The general `rank_union degree = Σ_block rank_block degree`
(`∀ degree >= 1`, arbitrary letter-disjoint blocks) rests on whole-word monochromaticity (no chain over a
disjoint union mixes letters from different blocks) plus a disjoint-filter-length lemma — resisting
induction identically to r10's two-block `disjointUnionAdditivityIsNamedNode`.

★ **FLIP (r15, literal delivery).**  The TWO-BLOCK self-loop instance is now DELIVERED `∀ degree ≥ 1`
(`twoBlockDisjointAdditivity`, `AcyclicTruncationDownwardClosureAndBlockAdditivity`) via whole-word
monochromaticity (`guardUnionForwardToBlock`) + the disjoint-filter-length lemma (`filterOrLengthSplit`); the
GENERAL `k`-block additivity over arbitrary letter-disjoint blocks stays NAMED.  `Bool := true` unchanged.

Read the meaning from THIS docstring.  `= true`. -/
def naryDisjointAdditivityGeneralIsNamedNode : Bool := true

/-! ### The TOWER-ANICK (#2144) r12 ledger — residual (0) DELIVERED, the general node still NAMED

  * **A — THE n-ary ENUMERATOR**: SHIPPED.  `allWordsOverAlphabet` (the ONE new def, alphabet as data) +
    `multiObstructionChainsAtDegreeOver` / `multiObstructionChainRankOracleOver` (the r3 pipeline
    re-based; the guard reused VERBATIM).
  * **B — THE n-ary LENGTH BRIDGE**: SHIPPED.  `memAppendCases` (the honest `++` splitter the
    variable-arity `map` forces), `memMapConsHasLength`, `memFlatMapWordsOverAlphabetHasLength`, ★★
    `memWordsOverAlphabetHasLength` (`word ∈ allWordsOverAlphabet alphabet n ==> word.length = n`), all
    via the `List.Mem`-constructor route, all `#print axioms`-clean.
  * **C — THE SUBSUMPTION HEADLINE**: SHIPPED.  ★★ `binaryEnumeratorAgrees` (`allWordsOverAlphabet
    [0, 1] n = allWordsOfLength n`) + `binaryOracleAgrees` (the oracle subsumes the shipped binary one) —
    every r3/r5/r6/r10 binary census recovered by specialization at `[0, 1]`, no regression.
  * **D — THE n-ary CENSUSES**: SHIPPED.  `naryCompleteGraphCensus` (`3^(d+1)`: `3, 9, 27, 81, 243`),
    `naryDisjointUnionCensus` + `naryDisjointUnionListSplitAndAdditivity` (three-block union `3, 3, 3, 3,
    3`, list split + additivity `rfl`, degree 0 excluded), `binaryRegressionCensus` (`[0, 1]` reproduces
    Fibonacci + `{xy}`) — all truth-probed by an independent enumeration BEFORE proving.
  * **E — THE RECONNECTION**: SHIPPED.  `dagChainNaryCensus` (`4, 3, 2, 1`) +
    `dagChainNaryCensusZeroAtDegreeFour`, `diamondNaryCensus` (`4, 4, 2, 0`),
    `threeCycleNaryCensusIsConstant` (`3, 3, 3, 3, 3, 3`, never truncates — the honest converse) — the
    r11 hostile graphs seen at their TRUE alphabet, healing FINDING A.
  * **F — THE CENSUS -> EXACTNESS BRIDGE**: SHIPPED.  `censusZeroImpliesExactOver` (mirrors r6, no Smith
    surgery) + `dagChainExactAtDegreeFour` / `diamondExactAtDegreeThree`.
  * **G — this ledger**: SHIPPED.

### Still WALLED (NAMED, never papered)

  * residual (ii) checker saturation, residual (iii) the topological-sort longest-path bound, and the
    final assembly (0)+(i)+(ii)+(iii) — all NAMED in the r11
    `generalGraphSoundnessResidualsAfterPigeonhole` (whose (0) marker flips to DELIVERED in its own
    docstring, the honest-record convention).
  * `naryDisjointAdditivityGeneralIsNamedNode` — the GENERAL `∀ degree >= 1` k-block additivity (the
    concrete 3-block seed is shipped).

### Honest scoping (no overclaim)

r12 delivers residual (0) of the r11 pigeonhole node: the n-ary alphabet enumerator + the re-based census
oracle, PROVEN to subsume the shipped binary enumerator (so no regression), with the reconnection
corollaries healing FINDING A's alphabet-blind censuses.  It does NOT close residuals (ii)/(iii), the
final assembly, nor the general k-block additivity — all NAMED.  Everything `rfl` / structural
(`List.Mem` constructors, `flatMap`/`map` reduction, scoped `maxRecDepth` for the compute-heavy censuses)
— no new propext surface, no Smith import, no lane-law violation. -/

/-- ★ **The TOWER-ANICK (#2144) r12 ledger marker.**  What stands, zero-axiom, additively over r11:
residual (0) of `generalGraphSoundnessResidualsAfterPigeonhole` — the n-ary alphabet enumerator
`allWordsOverAlphabet` (the ONE new def) + the re-based census oracle, its n-ary length bridge
(`memAppendCases` / `memMapConsHasLength` / `memFlatMapWordsOverAlphabetHasLength` /
`memWordsOverAlphabetHasLength`, `List.Mem`-constructor route), ★★ the SUBSUMPTION
(`binaryEnumeratorAgrees` / `binaryOracleAgrees` — the n-ary oracle recovers the shipped binary one, no
regression), the n-ary censuses (`naryCompleteGraphCensus` `3^(d+1)`, `naryDisjointUnionCensus` +
three-block list split / additivity, `binaryRegressionCensus`), the reconnection corollaries
(`dagChainNaryCensus` / `diamondNaryCensus` truncating at their TRUE longest path,
`threeCycleNaryCensusIsConstant` never truncating), and the n-ary census -> exactness bridge
(`censusZeroImpliesExactOver`).  Residuals NAMED (checker saturation (ii), the longest-path bound (iii),
the final assembly, and the general k-block additivity), never papered.  Read the meaning from THIS
docstring (the honest-record convention). -/
def naryAlphabetObstructionChainEnumeratorIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
