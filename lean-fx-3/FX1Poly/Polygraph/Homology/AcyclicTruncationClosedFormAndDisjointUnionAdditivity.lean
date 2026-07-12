import FX1Poly.Polygraph.Homology.AcyclicObstructionTruncationCertificate

/-! # FX1Poly/Polygraph/Homology/AcyclicTruncationClosedFormAndDisjointUnionAdditivity — the `{xy}`
    fuel-soundness CLOSED FORM (crossing the five-round `flatMap`-membership wall) and the
    disjoint-union Mayer-Vietoris additivity SEED (TOWER-ANICK r10, #2144 / #2145)

The r6 file `AcyclicObstructionTruncationCertificate` shipped the decidable Ufnarovski-graph acyclicity
checker (`isAcyclicUfnarovskiGraph`, fuel-structural), the conditional vanishing `census 0 ==> exact`
(`censusZeroImpliesExact`), and the `{xy}` FINITE eventual-exactness window (degrees `2..5`,
`linearSystemEventuallyExact`).  It NAMED the general `acyclic ==> census 0` closed form
(`acyclicToCensusZeroIsNamedNode`), reducing it to two ingredients: (a) the `allWordsOfLength` length
lemma `word ∈ allWordsOfLength n ==> word.length = n`, and (b) the filter-empties step.  Ingredient (a)
had stood NAMED for FIVE rounds as "the lane's `flatMap`-membership propext minefield" — the stock Init
`iff` lemmas `List.mem_flatMap` / `List.mem_append` / `List.filter_cons` / `List.length_filter_le` each
leak `propext`.

## What this module CROSSES (the five-round wall, zero-axiom)

The propext leak was an artifact of the stock `iff` lemmas — NOT of the mathematics.  The `List.Mem`
constructor route (`List.Mem.head` / `List.Mem.tail` `cases`, the lane's load-bearing discipline for
`WalkerChainComplex` / `CyclicThreeChainComplex`) walks straight through it.  This module builds:

  * `memFlatMapWordsHasLength` / `memWordsHasLength` — ★ THE CROSSED WALL: `word ∈ allWordsOfLength n
    ==> word.length = n`, by outer induction on `n` and an inner list-induction on
    `allWordsOfLength n`, decomposing the `flatMap`-cons `(base :: rest).flatMap gen = 0 :: base ::
    1 :: base :: rest.flatMap gen` DEFINITIONALLY (`rfl`) and destructuring the `List.Mem` witness
    through its three concrete constructor shapes.  No `mem_flatMap`, no `mem_append`.
  * `filterAllFalseIsNil` — the filter-empties step: a list all of whose elements fail the predicate
    filters to `[]`, structural on the list via `unfold List.filter` (NOT `List.filter_cons`).
  * `linearGuardFalseOnLengthGeThree` — lifts the shipped `{xy}` truncation criterion
    `noLinearChainOfLengthThreeOrMore` to ANY word of length `≥ 3`.
  * `linearCensusZeroAboveDegreeOne` — ★★ THE `{xy}` CLOSED FORM: `∀ degree, 2 ≤ degree ==>
    multiObstructionChainRankOracle {xy} degree = 0`, discharging the general-`∀ d` truncation for the
    `{xy}` instance (every degree-`degree + 1` word is longer than the longest path `1`, so the guard
    fails and the filter empties).  This is the honest LITERAL delivery that flips the `{xy}` case of
    the r6 named node `acyclicToCensusZeroIsNamedNode` (docstring recorded in the owning file).
  * `linearSystemExactAboveDegreeOne` — ★★ upgrades r6's FINITE eventual-exactness window (`2..5`) to
    `∀ degree ≥ 2` (`censusZeroImpliesExact` composed with the closed form).
  * `linearAcyclicImpliesTruncation` — the FUEL-SOUNDNESS instance: the checker verdict
    `isAcyclicUfnarovskiGraph {xy} 2 = true` IS sound for the one shipped acyclic graph.

## The disjoint-union Mayer-Vietoris SEED (truth-probed by `#eval` FIRST)

Over disjoint letter blocks `{xx} = [(0, 0)]` (letter `0`), `{yy} = [(1, 1)]` (letter `1`), and their
union `{xx, yy}`, the chains are MONOCHROMATIC: an adjacency-obstruction chain over the union cannot mix
letters (a cross-letter pair `(0, 1)` / `(1, 0)` is not an obstruction, so the guard kills it).  The
`#eval` ground truth (degrees `0..4`): `{xx}` and `{yy}` both `2, 1, 1, 1, 1`; the union `2, 2, 2, 2,
2`; and the union chain list is LITERALLY the disjoint concatenation `chains_xx ++ chains_yy` for every
`degree ≥ 1`.  The concrete rung ships:

  * `xxSystem` / `yySystem` / `unionSystem` — the disjoint-block obstruction data.
  * `mvCensuses` — the census values (`{xx} 2 = 1`, `{yy} 2 = 1`, union `2, 2, 2` at degrees `2, 3, 4`).
  * `mvListSplitAndAdditivity` — ★ the concrete Mayer-Vietoris witnesses: `chains_union 2 = chains_xx 2
    ++ chains_yy 2` (the monochromatic list split) and `rank_union 3 = rank_xx 3 + rank_yy 3` (rank
    additivity), both `rfl` on the computed lists.

Degree `0` is EXCLUDED from additivity: there the count is `2 ≠ 1 + 1` (the fixed `{0, 1}`-alphabet
degree-0 double-count, an artifact flagged lane-wide), so additivity holds only for `degree ≥ 1`.

## Honest scope (NO overclaim — the standing walls stay NAMED)

This is the MONOMIAL `{xy}` instance of the general `acyclic ==> census 0` soundness plus the concrete
two-block Mayer-Vietoris seed.  It does NOT close:

  * `generalGraphLongestPathBoundIsNamedNode` — the GENERAL-graph soundness (an arbitrary acyclic
    Ufnarovski graph truncates above its longest path).  That needs three separately-hard zero-axiom
    proofs recorded in its docstring: the classical pigeonhole (`listOverCarrierRepeats`), checker
    saturation, and the topological-sort longest-path bound.  The `{xy}` instance discharges it here
    with the bespoke `noLinearChainOfLengthThreeOrMore` in place of the pigeonhole (longest path `1`,
    carrier `{0, 1}`).
  * `disjointUnionAdditivityIsNamedNode` — the GENERAL `∀ degree ≥ 1` additivity (`rank_union degree =
    rank_xx degree + rank_yy degree`).  The pointwise guard split `guard_union = guard_xx || guard_yy`
    is TRUE but resists induction (it rests on whole-word monochromaticity) and needs a
    disjoint-filter-length lemma; its skeleton is recorded in the docstring.

The r5 / r6 theorem bodies stay verbatim UNMOVED (this module is additive); the r6 named node
`acyclicToCensusZeroIsNamedNode` flips ONLY in its own docstring (the `{xy}` instance now delivered,
the general-graph case still named).

## Zero-axiom design decisions

  * Membership is BUILT and DESTRUCTURED by `List.Mem.head` / `List.Mem.tail` constructors — never
    `decide` on `List.Mem` (leaks `propext`), never the `mem_*` `iff` lemmas.
  * The `flatMap`-cons reduction `(base :: rest).flatMap gen = 0 :: base :: 1 :: base :: rest.flatMap
    gen` is DEFINITIONAL (`rfl`); length arms are `congrArg (fun measured => measured + 1)` — never
    `simp [List.length_cons]` (leaks `propext`).
  * `filterAllFalseIsNil` reduces the filter head via `unfold List.filter; rw [hHeadFalse]` — never
    `List.filter_cons` (leaks `propext`).
  * The short-word arms of `linearGuardFalseOnLengthGeThree` refute `3 ≤ length` with the explicit
    `Nat.not_succ_le_zero` / `Nat.le_of_succ_le_succ` chain — never `by decide` (a free letter in the
    word list stalls the decidability instance).
  * `linearCensusZeroAboveDegreeOne` closes `[].length = 0` with a trailing `rfl` after `rw
    [hChainsEmpty]` (the rewrite's auto-`rfl` runs at reducible transparency and does not unfold
    `List.length`).
  * The Mayer-Vietoris list split / additivity are `rfl` on the COMPUTED lists — never `==` /
    `DecidableEq` on `List (List Nat)` (`List.append_nil` / `List.length_append` leak `propext`).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (fuel `Nat` / path list).  Per-declaration gated (and independently `#print axioms`-checked
for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/AcyclicTruncationClosedFormAndDisjointUnionAdditivity.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## A — the CROSSED WALL: the `flatMap`-membership length bridge (`List.Mem`-constructor route) -/

/-- The inner list-induction of the length bridge: if every base word of `wordsList` has length
`length`, then every word of `wordsList.flatMap (fun word => [0 :: word, 1 :: word])` has length
`length + 1`.  Structural on `wordsList`; the `flatMap`-cons reduces DEFINITIONALLY to `0 :: base ::
1 :: base :: remainingBases.flatMap gen`, and the `List.Mem` witness is destructured through its three
concrete constructor shapes (`head`, `tail head`, `tail tail`) — never `List.mem_flatMap` /
`List.mem_append` (both leak `propext`). -/
theorem memFlatMapWordsHasLength (length : Nat) :
    ∀ (wordsList : List (List Nat)),
      (∀ base, base ∈ wordsList → base.length = length) →
      ∀ resultWord,
        resultWord ∈ wordsList.flatMap (fun word => [0 :: word, 1 :: word]) →
        resultWord.length = length + 1
  | [], _, _, hMem => by
      have hMemNil : _ ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | base :: remainingBases, hAllBaseLen, _, hMem => by
      have hBaseLen : base.length = length := hAllBaseLen base (List.Mem.head remainingBases)
      cases hMem with
      | head => exact congrArg (fun measured => measured + 1) hBaseLen
      | tail _ hMemSecond =>
          cases hMemSecond with
          | head => exact congrArg (fun measured => measured + 1) hBaseLen
          | tail _ hMemRest =>
              exact memFlatMapWordsHasLength length remainingBases
                (fun candidate hCandidate =>
                  hAllBaseLen candidate (List.Mem.tail base hCandidate))
                _ hMemRest

/-- ★★ **THE CROSSED WALL** (five rounds NAMED): `word ∈ allWordsOfLength targetLength ==>
word.length = targetLength`.  Outer STRUCTURAL induction on `targetLength` (`0 => [[]]`, the singleton
`[]`; `n + 1 => flatMap`, delegated to `memFlatMapWordsHasLength`).  The `allWordsOfLength`
`flatMap`-membership propext minefield, dissolved via the `List.Mem`-constructor route. -/
theorem memWordsHasLength :
    ∀ (targetLength : Nat) (word : List Nat),
      word ∈ allWordsOfLength targetLength → word.length = targetLength
  | 0, word, hMem => by
      have hMemSingleton : word ∈ ([[]] : List (List Nat)) := hMem
      cases hMemSingleton with
      | head => rfl
      | tail _ hMemTail => cases hMemTail
  | targetLength + 1, word, hMem =>
      memFlatMapWordsHasLength targetLength (allWordsOfLength targetLength)
        (fun base hBase => memWordsHasLength targetLength base hBase) word hMem

/-! ## B — the filter-empties step and the length-`≥ 3` guard failure -/

/-- **The filter-empties step**: a list all of whose elements fail the predicate filters to `[]`.
Structural on the list; the filter head is reduced via `unfold List.filter; rw [hHeadFalse]` — never
`List.filter_cons` (leaks `propext`).  Membership is built with `List.Mem.head` / `List.Mem.tail`. -/
theorem filterAllFalseIsNil {carrier : Type} (predicate : carrier → Bool) :
    ∀ (items : List carrier),
      (∀ element, element ∈ items → predicate element = false) →
      items.filter predicate = []
  | [], _ => rfl
  | head :: remainingItems, hAllFalse => by
      have hHeadFalse : predicate head = false :=
        hAllFalse head (List.Mem.head remainingItems)
      have hRecEmpty : remainingItems.filter predicate = [] :=
        filterAllFalseIsNil predicate remainingItems
          (fun element hElement => hAllFalse element (List.Mem.tail head hElement))
      show (head :: remainingItems).filter predicate = []
      unfold List.filter
      rw [hHeadFalse]
      exact hRecEmpty

/-- **The `{xy}` guard fails on every word of length `≥ 3`**: lifts the shipped truncation criterion
`noLinearChainOfLengthThreeOrMore` (bespoke to a `firstLetter :: secondLetter :: thirdLetter :: rest`
head) to ANY word once its length reaches `3`.  The short-word arms refute `3 ≤ length` with the
explicit `Nat.not_succ_le_zero` / `Nat.le_of_succ_le_succ` chain (never `by decide`, which stalls on
the free letter). -/
theorem linearGuardFalseOnLengthGeThree :
    ∀ (word : List Nat), 3 ≤ word.length →
      allAdjacentPairsAreObstructions linearObstructionSystem word = false
  | [], hLen => (Nat.not_succ_le_zero 2 hLen).elim
  | [_], hLen => (Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ hLen)).elim
  | [_, _], hLen =>
      (Nat.not_succ_le_zero 0
        (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hLen))).elim
  | firstLetter :: secondLetter :: thirdLetter :: remainingLetters, _ =>
      noLinearChainOfLengthThreeOrMore firstLetter secondLetter thirdLetter remainingLetters

/-! ## C — the `{xy}` fuel-soundness CLOSED FORM (the flip of the r6 named node's `{xy}` instance) -/

/-- ★★ **THE `{xy}` TRUNCATION CLOSED FORM**: `∀ degree, 2 ≤ degree ==>
multiObstructionChainRankOracle linearObstructionSystem degree = 0`.  Every candidate word at degree
`degree` has length `degree + 1 ≥ 3` (`memWordsHasLength`), so it fails the `{xy}` guard
(`linearGuardFalseOnLengthGeThree`), so the chain filter empties (`filterAllFalseIsNil`) and the rank
is `0`.  This is the general-`∀ d` truncation for the `{xy}` instance, discharging r5's
`allDegreesTruncationClosedFormIsNamedNode` and the `{xy}` case of r6's
`acyclicToCensusZeroIsNamedNode`.  Zero-axiom, no `flatMap`-membership `iff` lemma. -/
theorem linearCensusZeroAboveDegreeOne :
    ∀ degree, 2 ≤ degree →
      multiObstructionChainRankOracle linearObstructionSystem degree = 0 := by
  intro degree hTwoLeDegree
  have hChainsEmpty :
      multiObstructionChainsAtDegree linearObstructionSystem degree = [] := by
    show (allWordsOfLength (degree + 1)).filter
        (allAdjacentPairsAreObstructions linearObstructionSystem) = []
    apply filterAllFalseIsNil
    intro word hWordMem
    have hWordLen : word.length = degree + 1 :=
      memWordsHasLength (degree + 1) word hWordMem
    have hThreeLeLen : 3 ≤ word.length := by
      rw [hWordLen]; exact Nat.succ_le_succ hTwoLeDegree
    exact linearGuardFalseOnLengthGeThree word hThreeLeLen
  show (multiObstructionChainsAtDegree linearObstructionSystem degree).length = 0
  rw [hChainsEmpty]
  rfl

/-- ★★ **THE `{xy}` FULL EVENTUAL EXACTNESS** (upgrades r6's finite window): `∀ degree, 2 ≤ degree ==>
isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem degree)`.  Composes the
closed form `linearCensusZeroAboveDegreeOne` with the shipped conditional vanishing
`censusZeroImpliesExact`, promoting r6's finite eventual-exactness window (`linearSystemEventuallyExact`,
degrees `2..5`) to the whole tail `degree ≥ 2` — the finite-global-dimension algebra `k⟨x, y⟩/(xy)`
becoming exact everywhere above its top degree, the opposite extreme from `fibMonomialNeverExact`. -/
theorem linearSystemExactAboveDegreeOne :
    ∀ degree, 2 ≤ degree →
      isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem degree) :=
  fun degree hTwoLeDegree =>
    censusZeroImpliesExact linearObstructionSystem degree
      (linearCensusZeroAboveDegreeOne degree hTwoLeDegree)

/-- ★ **THE FUEL-SOUNDNESS INSTANCE**: the acyclicity checker's verdict IS sound for the one shipped
acyclic graph — `isAcyclicUfnarovskiGraph linearObstructionSystem 2 = true ==> ∀ degree, 2 ≤ degree ==>
multiObstructionChainRankOracle linearObstructionSystem degree = 0`.  The hypothesis is the shipped
`rfl`-true `linearGraphIsAcyclic`; the conclusion is the closed form.  This is the `{xy}` witness of the
general checker-soundness bridge (the GENERAL bridge stays `generalGraphLongestPathBoundIsNamedNode`). -/
theorem linearAcyclicImpliesTruncation :
    isAcyclicUfnarovskiGraph linearObstructionSystem 2 = true →
      ∀ degree, 2 ≤ degree →
        multiObstructionChainRankOracle linearObstructionSystem degree = 0 :=
  fun _ degree hTwoLeDegree => linearCensusZeroAboveDegreeOne degree hTwoLeDegree

/-! ## D — the disjoint-union Mayer-Vietoris SEED (truth-probed by `#eval` before proving) -/

/-- The `{xx}` disjoint block `[(0, 0)]` over letter `0` — a self-loop, chain count constant `1` above
degree `0` (the same shape as `singleObstructionUnarySystem`, named freshly for the Mayer-Vietoris
statement). -/
def xxSystem : List (Nat × Nat) := [(0, 0)]

/-- The `{yy}` disjoint block `[(1, 1)]` over letter `1` — the letter-disjoint twin of `xxSystem`. -/
def yySystem : List (Nat × Nat) := [(1, 1)]

/-- The disjoint UNION `{xx, yy} = [(0, 0), (1, 1)]` — two self-loops on DISJOINT letters, so its chains
are the disjoint union of the two blocks' chains (no chain mixes letters `0` and `1`). -/
def unionSystem : List (Nat × Nat) := [(0, 0), (1, 1)]

/-- ★ **The Mayer-Vietoris census** (`rfl` on `ℕ` literals): each block `{xx}` / `{yy}` has degree-2
count `1`, and the union has count `2` at degrees `2, 3, 4` — the disjoint blocks contributing one
monochromatic chain each, summing to `2`. -/
theorem mvCensuses :
    multiObstructionChainRankOracle xxSystem 2 = 1 ∧
    multiObstructionChainRankOracle yySystem 2 = 1 ∧
    multiObstructionChainRankOracle unionSystem 2 = 2 ∧
    multiObstructionChainRankOracle unionSystem 3 = 2 ∧
    multiObstructionChainRankOracle unionSystem 4 = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **THE MAYER-VIETORIS SEED**: the disjoint-union chains split as a LIST concatenation and the ranks
ADD.  `multiObstructionChainsAtDegree unionSystem 2 = chains {xx} 2 ++ chains {yy} 2` (the union chain
list `[[0, 0, 0], [1, 1, 1]]` is literally `[[0, 0, 0]] ++ [[1, 1, 1]]` — every union chain is
monochromatic, so no cross terms), and `rank_union 3 = rank_xx 3 + rank_yy 3` (`2 = 1 + 1`).  Both
`rfl` on the COMPUTED lists (never `==` on `List (List Nat)`).  Degree `≥ 1` only — degree `0` has the
fixed-alphabet double-count `2 ≠ 1 + 1` (excluded, flagged lane-wide).  The concrete coproduct /
Mayer-Vietoris structure; the general `∀ degree ≥ 1` additivity stays
`disjointUnionAdditivityIsNamedNode`. -/
theorem mvListSplitAndAdditivity :
    multiObstructionChainsAtDegree unionSystem 2
      = multiObstructionChainsAtDegree xxSystem 2
          ++ multiObstructionChainsAtDegree yySystem 2 ∧
    multiObstructionChainRankOracle unionSystem 3
      = multiObstructionChainRankOracle xxSystem 3
          + multiObstructionChainRankOracle yySystem 3 :=
  ⟨rfl, rfl⟩

/-! ## E — the standing walls (NAMED, with recorded zero-axiom skeletons) and the r10 NODE-3 ledger -/

/-- ★ **The general-graph `acyclic ==> census 0` soundness is a NAMED node.**  The `{xy}` instance is
SHIPPED (`linearAcyclicImpliesTruncation` / `linearCensusZeroAboveDegreeOne`) with the bespoke
`noLinearChainOfLengthThreeOrMore` standing in for the pigeonhole (longest path `1`, carrier `{0, 1}`).
The GENERAL statement `isAcyclicUfnarovskiGraph edges vertexCount = true ==> ∀ degree, vertexCount ≤
degree ==> multiObstructionChainRankOracle edges degree = 0` needs THREE separately-hard zero-axiom
proofs:

  (i) **the classical pigeonhole** `listOverCarrierRepeats`: a walk over a finite vertex carrier longer
      than the carrier repeats a vertex.  Recorded skeleton: carrier-induction with a hand-rolled
      `countOccurrences : Nat → List Nat → Nat` and the propext-clean `removeFirst` (both over
      `natEqBool`), invariant "`carrier.length < walk.length` ==> some vertex occurs `≥ 2` times",
      membership destructured by `List.Mem.head` / `List.Mem.tail` `cases` (never `decide`).  A
      genuinely substantial proof — its own round.
  (ii) **checker saturation**: that `obstructionReachableWithin edges vertexCount` captures ALL
      reachable vertices (a fixpoint the current `++`-fold does not obviously give).
  (iii) **the topological-sort longest-path bound**: an acyclic graph's longest walk is `≤ vertexCount`,
      so chains die above it.

★ **FLIP (r14, literal delivery).**  All three ingredients are now supplied and ASSEMBLED: (i)
`listOverCarrierRepeats` (r11), (ii)+(iii) `closedEdgeWalkImpliesCheckerFalse` (r13, the loose single-fuel
bound subsuming saturation), and the closed form `acyclicCensusZeroAboveAlphabetLength` (r14,
`AcyclicSystemTruncationCertificate`).  The delivered statement is the FINDING-A-healed n-ary form
(`isAcyclicUfnarovskiGraph edges alphabet.length = true ==> ∀ degree, alphabet.length ≤ degree ==>
multiObstructionChainRankOracleOver alphabet edges degree = 0`), at the LOOSE bound `alphabet.length` — the
literal binary-`vertexCount` `multiObstructionChainRankOracle` phrasing above is SUPERSEDED by the n-ary
oracle (r12's FINDING A), not itself re-proved.  `acyclicSystemExactAboveAlphabetLength` lifts it to
eventual exactness (monomial/zero-boundary model); the general-CONVERGENT tower
(`generalTelescopeHomologyIsNamedNode`) stays OPEN.  `Bool := true` unchanged (the honest-record convention).

Read the meaning from THIS docstring.  `= true`. -/
def generalGraphLongestPathBoundIsNamedNode : Bool := true

/-- ★ **The general `∀ degree ≥ 1` disjoint-union additivity is a NAMED node.**  The concrete witnesses
are SHIPPED (`mvListSplitAndAdditivity`: the degree-2 list split + the degree-3 rank additivity, both
`rfl`).  The general `rank_union degree = rank_xx degree + rank_yy degree` (`∀ degree ≥ 1`) rests on TWO
non-trivial pieces recorded here:

  (a) **whole-word monochromaticity**: no chain over `unionSystem` mixes letters `0` and `1` (a
      cross-letter adjacency `(0, 1)` / `(1, 0)` is not an obstruction, so the guard kills it) — hence
      the pointwise guard split `guard_union word = guard_xx word || guard_yy word` holds (it FAILS to
      induct naively: `cases firstLetter <;> cases secondLetter <;> simp` leaks `propext` + `sorry`,
      because `∧ (aᵢ || bᵢ) ≠ (∧ aᵢ) || (∧ bᵢ)` without the monochromaticity).
  (b) **a disjoint-filter-length lemma**: `(∀ element ∈ items, ¬ (predicateA element ∧ predicateB
      element)) ==> (items.filter (predicateA || predicateB)).length = (items.filter predicateA).length
      + (items.filter predicateB).length`, structural, the disjointness holding only for length-`≥ 2`
      words (excluding the degree-0 double-count).

Read the meaning from THIS docstring.  `= true`. -/
def disjointUnionAdditivityIsNamedNode : Bool := true

/-! ### The TOWER-ANICK (#2144 / #2145) r10 NODE-3 ledger — bricks shipped, residuals named

  * **A — THE CROSSED WALL**: SHIPPED.  `memFlatMapWordsHasLength` + `memWordsHasLength` (`word ∈
    allWordsOfLength n ==> word.length = n`), crossing the five-round `flatMap`-membership propext
    minefield via the `List.Mem`-constructor route.
  * **B — THE FILTER-EMPTIES STEP**: SHIPPED.  `filterAllFalseIsNil` (`unfold List.filter`, not
    `List.filter_cons`) + `linearGuardFalseOnLengthGeThree` (the shipped criterion lifted to length
    `≥ 3`).
  * **C — THE `{xy}` CLOSED FORM**: SHIPPED.  ★★ `linearCensusZeroAboveDegreeOne` (`∀ degree ≥ 2,
    census {xy} = 0`), ★★ `linearSystemExactAboveDegreeOne` (full eventual exactness `∀ degree ≥ 2`,
    upgrading r6's finite `2..5` window), and `linearAcyclicImpliesTruncation` (the fuel-soundness
    instance for the one acyclic graph).
  * **D — THE MAYER-VIETORIS SEED**: SHIPPED.  `xxSystem` / `yySystem` / `unionSystem`, `mvCensuses`,
    ★ `mvListSplitAndAdditivity` (the monochromatic list split + rank additivity, `rfl`), truth-probed
    by `#eval` FIRST (census `2, 1, 1, 1, 1` / `2, 2, 2, 2, 2`; additivity true `∀ degree ≥ 1`).
  * **E — this ledger**: SHIPPED.  Every deferral a NAMED node with a recorded zero-axiom skeleton.

### Still WALLED (NAMED, never papered)

  * `generalGraphLongestPathBoundIsNamedNode` — the GENERAL-graph `acyclic ==> census 0` soundness (the
    pigeonhole `listOverCarrierRepeats` + checker saturation + the topological-sort longest-path bound).
    The `{xy}` instance is discharged here; the general one needs three separately-hard rounds.
  * `disjointUnionAdditivityIsNamedNode` — the GENERAL `∀ degree ≥ 1` additivity (whole-word
    monochromaticity + a disjoint-filter-length lemma).  The concrete seed is shipped.

### Honest scoping (no overclaim)

r10 NODE-3 crosses the five-round `flatMap`-membership wall zero-axiom and delivers the `{xy}` instance
of the r6 named node `acyclicToCensusZeroIsNamedNode` (its docstring flips to record the `{xy}` case
shipped, general-graph case still named), upgrades r6's finite eventual-exactness window to the whole
tail, and seeds the disjoint-union Mayer-Vietoris structure with concrete `rfl` witnesses.  It does NOT
close the general-graph soundness nor the general additivity — both NAMED with recorded skeletons.
Everything `rfl` / structural (`List.Mem` constructors, `unfold List.filter`, fuel/list recursion) — no
new propext surface. -/

/-- ★ **The TOWER-ANICK (#2144 / #2145) r10 NODE-3 ledger marker.**  What stands, zero-axiom, additively
over r6: THE CROSSED WALL (`memWordsHasLength`, five rounds NAMED, via the `List.Mem`-constructor
route); THE `{xy}` FUEL-SOUNDNESS CLOSED FORM (`linearCensusZeroAboveDegreeOne` — `∀ degree ≥ 2,
census {xy} = 0`; `linearSystemExactAboveDegreeOne` — full eventual exactness upgrading r6's `2..5`
window; `linearAcyclicImpliesTruncation` — the checker verdict IS sound for the one acyclic graph); and
THE DISJOINT-UNION MAYER-VIETORIS SEED (`mvListSplitAndAdditivity` — the monochromatic list split + rank
additivity, `rfl`, truth-probed by `#eval` first).  Residuals NAMED (the general-graph longest-path /
pigeonhole soundness, the general `∀ degree ≥ 1` additivity), each with a recorded zero-axiom skeleton,
never papered.  Read the meaning from THIS docstring (the honest-record convention). -/
def acyclicTruncationClosedFormAndDisjointUnionAdditivityIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
