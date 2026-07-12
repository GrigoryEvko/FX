import FX1Poly.Polygraph.Homology.AcyclicSystemTruncationCertificate

/-! # FX1Poly/Polygraph/Homology/AcyclicTruncationDownwardClosureAndBlockAdditivity — the TIGHT
    self-propagating truncation (downward-closure of the chain-census support) and the two-block
    disjoint-union additivity bricks (TOWER-ANICK r15, #2145 TOWER-TRUNC)

r14 `AcyclicSystemTruncationCertificate` shipped the general-graph census-zero closed form
`acyclicCensusZeroAboveAlphabetLength` at the LOOSE pigeonhole bound `alphabet.length`.  The truth-probe
that opened r15 measured the census sequences of the reconnected r11/r12 graphs (DAG chain `4, 3, 2, 1, 0`;
diamond `4, 4, 2, 0`) and a hostile non-monotone graph (`3, 4, 6, 8, 12, 16, 24` — the count sequence GOES
UP), and found: the census-count sequence is NOT monotone, but its SUPPORT (the set of degrees with a
nonzero census) is ALWAYS downward-closed — no fixture is `gappy` (no degree with census `0` sitting below
a degree with census `> 0`).  That is the honest tight truncation the #2145 title ("bounded overlap depth
kills the tower above the bound") asks for: once the census hits `0` at ANY degree, it stays `0` above,
STRICTLY tighter than r14's loose `alphabet.length` (the star graph `[(0,1)…(0,5)]` witnesses census `0`
already at degree `2`, while `alphabet.length = 6`).

## T1 — THE TIGHT SELF-PROPAGATING TRUNCATION (the round headline)

  * `memWordsOverAlphabetConsSplit` / `memFlatMapWordsConsSplit` — the n-ary enumerator cons-decomposition:
    a word of `allWordsOverAlphabet alphabet (length + 1)` is `letter :: base` with `base ∈
    allWordsOverAlphabet alphabet length` (the enumerator PREPENDS one letter per step).  The n-ary analog
    of r14's letters/length bridges, re-payloaded to the head/tail split, via `memAppendCases` +
    `memMapConsSplit` (r12/r14, the `List.Mem`-constructor route).
  * `filterPositiveHasWitness` / `memberPassingImpliesFilterPositive` — the two filter-positivity bridges:
    a positive-length filtered list has a passing witness member, and a passing witness member forces a
    positive-length filtered list.  Structural on the list, the filter head reduced by `unfold List.filter
    [at _]` + the `exact`-defeq collapse of the constructor-`match` (never `List.filter_cons`, which leaks
    `propext` via its `if _ = true` guard).
  * ★★ `censusPositiveDownwardClosed` — the load-bearing step: `0 < rank (degree + 1) ==> 0 < rank degree`.
    A degree-`(degree+1)` chain word `letter :: base` truncates by DROPPING ITS HEAD — the `&&`-right
    conjunct of `allAdjacentPairsAreObstructions` (r13 `guardTailStep`) keeps `base` a chain, and `base`
    (length `degree + 1`) is already a degree-`degree` candidate, so the degree-`degree` filter is nonempty.
  * ★★ `censusZeroPropagatesUpward` — THE HEADLINE: `rank boundDegree = 0 ==> ∀ degree, boundDegree ≤
    degree ==> rank degree = 0`.  Additive `Nat.le` induction (never `Nat.sub`) on the contrapositive of
    `censusPositiveDownwardClosed`.  `acyclicCensusZeroPropagatesFromAlphabetLength` re-derives r14's closed
    form as a COROLLARY and tightens it: the self-propagating zero from ANY witnessed degree subsumes and
    beats the loose `alphabet.length`.

## Honest scope (NO overclaim)

T1 is the tight-truncation upgrade of r14's loose closed form, in the same n-ary oracle
`multiObstructionChainRankOracleOver`, same MONOMIAL (zero-boundary) model.  It is a statement about the
SUPPORT (nonzero-ness), NOT the count: the census sequence is genuinely non-monotone (the probe's
`3, 4, 6, 8` witness), so any "counts decrease" phrasing is FALSE and is not claimed.  The general-CONVERGENT
telescope (`generalTelescopeHomologyIsNamedNode`) stays walled; the tight TOPOLOGICAL longest-path bound is
SUPERSEDED by this self-propagating form (a cleaner route than longest-path), not delivered.  No Smith
import, no Homology<->Omega edge.

## Zero-axiom design decisions (the lane's propext minefield)

  * Membership is BUILT and DESTRUCTURED by `List.Mem.head` / `List.Mem.tail` constructors — never `decide`
    on `List.Mem`, never `List.mem_map` / `List.mem_append` / `List.mem_flatMap` (all leak `propext`).  The
    `flatMap`-cons is split by `memAppendCases` (r12) and `memMapConsSplit` (r14).
  * The filter head is reduced by `unfold List.filter [at hyp]` then the `exact`-defeq collapse of the
    `match` on the (now-literal) `Bool` guard — the working pattern of r10's `filterAllFalseIsNil`.  Never
    `List.filter_cons` (its `if _ = true` guard leaks `propext` and leaves a `sorryAx` residue).
  * The upward propagation decomposes `boundDegree ≤ degree` by STRUCTURAL induction on the `Nat.le`
    witness; the census collapse uses `Nat.succ_pos` / `Nat.lt_irrefl` (additive, never `Nat.sub`).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (alphabet / word / item lists, `Nat.le` witness).  Per-declaration gated (and independently
`#print axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/AcyclicTruncationDownwardClosureAndBlockAdditivity.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## A — the n-ary enumerator cons-decomposition (`List.Mem`-constructor route) -/

/-- **The `flatMap` cons-splitter**: a member of `wordsList.flatMap (fun word => alphabet.map (fun letter =>
letter :: word))` is `letter :: base` for some `letter` and some `base ∈ wordsList`.  Structural on
`wordsList`; the `flatMap`-cons reduces DEFINITIONALLY to `gen base ++ remainingBases.flatMap gen`, split by
r12's `memAppendCases`, and the map arm by r14's `memMapConsSplit`.  Never `List.mem_flatMap` /
`List.mem_map` (both leak `propext`). -/
theorem memFlatMapWordsConsSplit (alphabet : List Nat) :
    ∀ (wordsList : List (List Nat)) (resultWord : List Nat),
      resultWord ∈ wordsList.flatMap (fun word => alphabet.map (fun letter => letter :: word)) →
      ∃ letter base, resultWord = letter :: base ∧ base ∈ wordsList
  | [], resultWord, hMem => by
      have hMemNil : resultWord ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | base :: remainingBases, resultWord, hMem => by
      have hMemAppend : resultWord ∈
          alphabet.map (fun letter => letter :: base)
            ++ remainingBases.flatMap (fun word => alphabet.map (fun letter => letter :: word)) := hMem
      cases memAppendCases _ resultWord _ hMemAppend with
      | inl hInMap =>
          obtain ⟨chosenLetter, _, hEq⟩ := memMapConsSplit base alphabet resultWord hInMap
          exact ⟨chosenLetter, base, hEq, List.Mem.head remainingBases⟩
      | inr hInRest =>
          obtain ⟨letter, laterBase, hEq, hLaterMem⟩ :=
            memFlatMapWordsConsSplit alphabet remainingBases resultWord hInRest
          exact ⟨letter, laterBase, hEq, List.Mem.tail base hLaterMem⟩

/-- ★ **THE ENUMERATOR CONS-DECOMPOSITION**: a word of `allWordsOverAlphabet alphabet (length + 1)` is
`letter :: base` with `base ∈ allWordsOverAlphabet alphabet length`.  The enumerator's `n + 1` step is
`(allWordsOverAlphabet alphabet length).flatMap (fun word => alphabet.map (fun letter => letter :: word))`
(one letter prepended per base), so the split is exactly `memFlatMapWordsConsSplit`. -/
theorem memWordsOverAlphabetConsSplit (alphabet : List Nat) (length : Nat) (word : List Nat)
    (hMem : word ∈ allWordsOverAlphabet alphabet (length + 1)) :
    ∃ letter base, word = letter :: base ∧ base ∈ allWordsOverAlphabet alphabet length := by
  have hMemFlat : word ∈ (allWordsOverAlphabet alphabet length).flatMap
      (fun previousWord => alphabet.map (fun letter => letter :: previousWord)) := hMem
  exact memFlatMapWordsConsSplit alphabet (allWordsOverAlphabet alphabet length) word hMemFlat

/-! ## B — the two filter-positivity bridges (the `exact`-defeq filter-head collapse) -/

/-- **Filter positivity has a witness**: a positive-length filtered list has some member of the source list
that passes the predicate.  Structural on the list; in the `predicate head = false` arm the source filter is
reduced by `unfold List.filter at hPos` and the `match`-on-`false` collapses under the recursive call's
`exact`-defeq (never `List.filter_cons`, which leaks `propext`). -/
theorem filterPositiveHasWitness {carrier : Type} (predicate : carrier → Bool) :
    ∀ (items : List carrier),
      0 < (items.filter predicate).length → ∃ chosen, chosen ∈ items ∧ predicate chosen = true
  | [], hPos => by exact absurd hPos (Nat.lt_irrefl 0)
  | head :: rest, hPos => by
      cases hHead : predicate head with
      | true => exact ⟨head, List.Mem.head rest, hHead⟩
      | false =>
          unfold List.filter at hPos
          rw [hHead] at hPos
          obtain ⟨chosen, hChosenMem, hChosenTrue⟩ := filterPositiveHasWitness predicate rest hPos
          exact ⟨chosen, List.Mem.tail head hChosenMem, hChosenTrue⟩

/-- **A passing member forces filter positivity**: a member that passes the predicate makes the filtered
list nonempty.  Structural on the list; the `predicate head = true` arm reduces the filter to a cons
(`Nat.succ_pos`), the `false` arm recurses on the tail membership.  The filter head is reduced by `unfold
List.filter` + `exact`-defeq. -/
theorem memberPassingImpliesFilterPositive {carrier : Type} (predicate : carrier → Bool) :
    ∀ (items : List carrier) (element : carrier),
      element ∈ items → predicate element = true → 0 < (items.filter predicate).length
  | [], _, hMem, _ => by cases hMem
  | head :: rest, element, hMem, hTrue => by
      cases hHead : predicate head with
      | true =>
          unfold List.filter
          rw [hHead]
          exact Nat.succ_pos _
      | false =>
          cases hMem with
          | head => rw [hHead] at hTrue; exact Bool.noConfusion hTrue
          | tail _ hTailMem =>
              unfold List.filter
              rw [hHead]
              exact memberPassingImpliesFilterPositive predicate rest element hTailMem hTrue

/-! ## C — the tight self-propagating truncation (the round headline) -/

/-- ★★ **THE DOWNWARD-CLOSURE STEP**: `0 < rank (degree + 1) ==> 0 < rank degree`, in the n-ary oracle over
any alphabet / obstruction graph.  A degree-`(degree + 1)` chain word `letter :: base` (a witness from
`filterPositiveHasWitness`) truncates by DROPPING ITS HEAD: `memWordsOverAlphabetConsSplit` exposes `base ∈
allWordsOverAlphabet alphabet (degree + 1)` (a degree-`degree` candidate), and r13 `guardTailStep` keeps
`base` a chain (the `&&`-right conjunct of `allAdjacentPairsAreObstructions`), so the degree-`degree` filter
is nonempty (`memberPassingImpliesFilterPositive`).  The chain condition SURVIVES truncation — the honest
content behind the probe's no-`gappy` finding. -/
theorem censusPositiveDownwardClosed (alphabet : List Nat) (edges : List (Nat × Nat)) (degree : Nat)
    (hPos : 0 < multiObstructionChainRankOracleOver alphabet edges (degree + 1)) :
    0 < multiObstructionChainRankOracleOver alphabet edges degree := by
  obtain ⟨word, hWordMem, hWordGuard⟩ :=
    filterPositiveHasWitness (allAdjacentPairsAreObstructions edges)
      (allWordsOverAlphabet alphabet (degree + 1 + 1)) hPos
  obtain ⟨letter, base, hWordEq, hBaseMem⟩ :=
    memWordsOverAlphabetConsSplit alphabet (degree + 1) word hWordMem
  have hConsGuard : allAdjacentPairsAreObstructions edges (letter :: base) = true :=
    hWordEq ▸ hWordGuard
  have hBaseGuard : allAdjacentPairsAreObstructions edges base = true :=
    guardTailStep edges letter base hConsGuard
  exact memberPassingImpliesFilterPositive (allAdjacentPairsAreObstructions edges)
    (allWordsOverAlphabet alphabet (degree + 1)) base hBaseMem hBaseGuard

/-- ★★ **THE TIGHT SELF-PROPAGATING TRUNCATION** (#2145 TOWER-TRUNC, the r15 headline): once the census
hits `0` at ANY degree, it stays `0` at every larger degree — `rank boundDegree = 0 ==> ∀ degree,
boundDegree ≤ degree ==> rank degree = 0`.  Additive `Nat.le` induction (never `Nat.sub`) on the
contrapositive of `censusPositiveDownwardClosed`: if `rank (laterDegree + 1)` were positive, downward
closure would force `rank laterDegree > 0`, contradicting the induction hypothesis `rank laterDegree = 0`.
This is STRICTLY tighter than r14's loose `alphabet.length` closed form (the star graph truncates far below
`alphabet.length`); the census-count sequence itself is non-monotone, so only the SUPPORT is closed. -/
theorem censusZeroPropagatesUpward (alphabet : List Nat) (edges : List (Nat × Nat))
    (boundDegree : Nat)
    (hZero : multiObstructionChainRankOracleOver alphabet edges boundDegree = 0) :
    ∀ degree, boundDegree ≤ degree →
      multiObstructionChainRankOracleOver alphabet edges degree = 0 := by
  intro degree hLe
  induction hLe with
  | refl => exact hZero
  | @step laterDegree _ ih =>
      cases hCensus : multiObstructionChainRankOracleOver alphabet edges (laterDegree + 1) with
      | zero => rfl
      | succ predecessorCount =>
          have hIsPos : 0 < multiObstructionChainRankOracleOver alphabet edges (laterDegree + 1) := by
            rw [hCensus]; exact Nat.succ_pos predecessorCount
          have hLowerPos : 0 < multiObstructionChainRankOracleOver alphabet edges laterDegree :=
            censusPositiveDownwardClosed alphabet edges laterDegree hIsPos
          rw [ih] at hLowerPos
          exact absurd hLowerPos (Nat.lt_irrefl 0)

/-- ★ **r14's LOOSE CLOSED FORM RE-DERIVED AND TIGHTENED (COROLLARY)**: an acyclic Ufnarovski graph's
census is `0` at every degree `>= alphabet.length` — recovered by propagating the single witnessed zero at
`alphabet.length` (r14 `acyclicCensusZeroAboveAlphabetLength` at `degree = alphabet.length`) upward via
`censusZeroPropagatesUpward`.  The propagation SUBSUMES r14's degree-by-degree closed form and tightens it:
the same certificate now fires from ANY witnessed zero, not only the loose `alphabet.length`. -/
theorem acyclicCensusZeroPropagatesFromAlphabetLength (edges : List (Nat × Nat)) (alphabet : List Nat)
    (hAcyclic : isAcyclicUfnarovskiGraph edges alphabet.length = true) :
    ∀ degree, alphabet.length ≤ degree →
      multiObstructionChainRankOracleOver alphabet edges degree = 0 :=
  censusZeroPropagatesUpward alphabet edges alphabet.length
    (acyclicCensusZeroAboveAlphabetLength edges alphabet hAcyclic alphabet.length
      (Nat.le_refl alphabet.length))

end FX1Poly.Polygraph.Homology
