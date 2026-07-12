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

## T2 — THE TWO-BLOCK DISJOINT-UNION ADDITIVITY (`∀ degree ≥ 1`)

  * `filterConsTrue` / `filterConsFalse` / `filterCongr` / `filterOrLengthSplit` — the filter-length toolkit:
    clean standalone filter-cons equations (via `generalize`-then-`unfold`, never `List.filter_cons`), filter
    congruence under pointwise-equal predicates, and ★★ the disjoint-`or` length split (`(filter (pA || pB)).
    length = (filter pA).length + (filter pB).length` under pointwise disjointness).
  * `isObstructionPairAppendSplit` / `guardAppendOfLeft` / `guardAppendOfRight` — the easy REVERSE direction
    (block-chain ⟹ union-chain), off `unionSystem = xxSystem ++ yySystem` and the pair-level `||` split.
  * ★★ `guardUnionForwardToBlock` — the hard FORWARD monochromaticity (union-chain ⟹ its unique block), by
    the lead-letter propagation `guardXxOfUnionLeadZero` / `guardYyOfUnionLeadOne`.
  * ★★ `guardUnionEqualsBlockOr` — the pointwise Bool identity `guard_union = guard_xx || guard_yy` (forward +
    reverse), and `guardBlocksDisjoint` — block disjointness on length-`≥ 2` words.
  * ★★ `twoBlockDisjointAdditivity` — THE HEADLINE: `rank_union degree = rank_xx degree + rank_yy degree` for
    every degree `≥ 1`, the `∀`-degree upgrade of r10's concrete seed `mvListSplitAndAdditivity`.

## Honest scope (NO overclaim)

T1 is the tight-truncation upgrade of r14's loose closed form, in the same n-ary oracle
`multiObstructionChainRankOracleOver`, same MONOMIAL (zero-boundary) model.  It is a statement about the
SUPPORT (nonzero-ness), NOT the count: the census sequence is genuinely non-monotone (the probe's
`3, 4, 6, 8` witness), so any "counts decrease" phrasing is FALSE and is not claimed.  T2 delivers the
self-loop two-block instance only; the general k-block additivity over arbitrary letter-disjoint blocks stays
NAMED (`naryDisjointAdditivityGeneralIsNamedNode`).  The general-CONVERGENT telescope
(`generalTelescopeHomologyIsNamedNode`) stays walled (T3 adjudication-only, no route); the tight TOPOLOGICAL
longest-path bound is SUPERSEDED by T1's self-propagating form (a cleaner route than longest-path), not
delivered.  No Smith import, no Homology<->Omega edge.

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

/-! ## D — the two-block disjoint-union additivity (the T2 leg)

The r10 seed `mvListSplitAndAdditivity` fixed the two-block self-loop union `{xx} = [(0,0)]`, `{yy} =
[(1,1)]`, `unionSystem = [(0,0),(1,1)]` (letter-disjoint) at CONCRETE degrees (`chains_union 2 = chains_xx 2
++ chains_yy 2`, `rank_union 3 = rank_xx 3 + rank_yy 3`), leaving the `∀ degree ≥ 1` rank additivity NAMED
(`disjointUnionAdditivityIsNamedNode`).  This section delivers that `∀ degree ≥ 1` additivity for the
self-loop two-block union.  The engine is the POINTWISE Bool identity `guard_union word = guard_xx word ||
guard_yy word` (`guardUnionEqualsBlockOr`), which rests on whole-word MONOCHROMATICITY: over letter-disjoint
self-loops on `{0, 1}`, a union-chain's first letter propagates through every adjacent pair (the shared
middle letter forces the same block), so a union-chain of length `≥ 2` is either all-`0` (an `xx`-chain) or
all-`1` (a `yy`-chain).  The forward direction `guardUnionForwardToBlock` (union-chain ⟹ its unique block)
is the genuinely-hard leg (the lead-letter propagation `guardXxOfUnionLeadZero` / `guardYyOfUnionLeadOne`);
the reverse (`guardAppendOfLeft` / `guardAppendOfRight`, off `unionSystem = xxSystem ++ yySystem` and the
pair-level `isObstructionPairAppendSplit`) is easy. -/

/-! ### D0 — clean standalone filter-cons equations + filter congruence + the disjoint-`or` length split -/

/-- **Filter-cons on a failing head**: `predicate head = false ==> (head :: rest).filter predicate =
rest.filter predicate`.  The `generalize rest.filter predicate = _` protects the folded tail so `unfold
List.filter` touches only the head and the `match`-on-`false` closes by `rw` — never `List.filter_cons`
(its `if _ = true` guard leaks `propext`). -/
theorem filterConsFalse {carrier : Type} (predicate : carrier → Bool) (head : carrier)
    (rest : List carrier) (hHead : predicate head = false) :
    (head :: rest).filter predicate = rest.filter predicate := by
  generalize hFolded : rest.filter predicate = filteredRest
  unfold List.filter
  rw [hHead, hFolded]

/-- **Filter-cons on a passing head**: `predicate head = true ==> (head :: rest).filter predicate = head ::
rest.filter predicate`.  Same `generalize`-then-`unfold` discipline as `filterConsFalse`. -/
theorem filterConsTrue {carrier : Type} (predicate : carrier → Bool) (head : carrier)
    (rest : List carrier) (hHead : predicate head = true) :
    (head :: rest).filter predicate = head :: rest.filter predicate := by
  generalize hFolded : rest.filter predicate = filteredRest
  unfold List.filter
  rw [hHead, hFolded]

/-- **Filter congruence**: predicates agreeing on every member give equal filtered lists.  Structural on the
list, the head reduced by `filterConsTrue` / `filterConsFalse`. -/
theorem filterCongr {carrier : Type} (predicateA predicateB : carrier → Bool) :
    ∀ (items : List carrier),
      (∀ element, element ∈ items → predicateA element = predicateB element) →
      items.filter predicateA = items.filter predicateB
  | [], _ => rfl
  | head :: rest, hAgree => by
      have hHeadEq : predicateA head = predicateB head := hAgree head (List.Mem.head rest)
      have hRest : rest.filter predicateA = rest.filter predicateB :=
        filterCongr predicateA predicateB rest
          (fun element hElement => hAgree element (List.Mem.tail head hElement))
      cases hCase : predicateA head with
      | true =>
          have hBTrue : predicateB head = true := hHeadEq ▸ hCase
          rw [filterConsTrue predicateA head rest hCase, filterConsTrue predicateB head rest hBTrue, hRest]
      | false =>
          have hBFalse : predicateB head = false := hHeadEq ▸ hCase
          rw [filterConsFalse predicateA head rest hCase, filterConsFalse predicateB head rest hBFalse, hRest]

/-- **The `(a + b) + 1 = (a + 1) + b` shuffle** (additive, `Nat.add_assoc` + `Nat.add_comm`, never
`Nat.sub`). -/
theorem natAddOnePullLeft (leftCount rightCount : Nat) :
    (leftCount + rightCount) + 1 = (leftCount + 1) + rightCount := by
  rw [Nat.add_assoc, Nat.add_comm rightCount 1, ← Nat.add_assoc]

/-- ★★ **THE DISJOINT-`or` LENGTH SPLIT**: if `predicateA` and `predicateB` never both hold on a member, the
length of the `(predicateA || predicateB)`-filter is the SUM of the two single-predicate filter lengths.
Structural on the list; each head case reduces the three filters by `filterConsTrue`/`filterConsFalse` and
shuffles the `+ 1` by `natAddOnePullLeft` / `Nat.add_assoc`.  The arithmetic core of the additivity. -/
theorem filterOrLengthSplit {carrier : Type} (predicateA predicateB : carrier → Bool) :
    ∀ (items : List carrier),
      (∀ element, element ∈ items → (predicateA element && predicateB element) = false) →
      (items.filter (fun element => predicateA element || predicateB element)).length
        = (items.filter predicateA).length + (items.filter predicateB).length
  | [], _ => rfl
  | head :: rest, hDisjoint => by
      have hRec : (rest.filter (fun element => predicateA element || predicateB element)).length
          = (rest.filter predicateA).length + (rest.filter predicateB).length :=
        filterOrLengthSplit predicateA predicateB rest
          (fun element hElement => hDisjoint element (List.Mem.tail head hElement))
      have hHeadDisjoint : (predicateA head && predicateB head) = false :=
        hDisjoint head (List.Mem.head rest)
      cases hA : predicateA head with
      | true =>
          have hB : predicateB head = false := by rw [hA] at hHeadDisjoint; exact hHeadDisjoint
          have hOr : (fun element => predicateA element || predicateB element) head = true := by
            show (predicateA head || predicateB head) = true
            rw [hA]; rfl
          rw [filterConsTrue _ head rest hOr, filterConsTrue predicateA head rest hA,
              filterConsFalse predicateB head rest hB]
          show (rest.filter (fun element => predicateA element || predicateB element)).length + 1
              = ((rest.filter predicateA).length + 1) + (rest.filter predicateB).length
          rw [hRec]
          exact natAddOnePullLeft _ _
      | false =>
          cases hB : predicateB head with
          | true =>
              have hOr : (fun element => predicateA element || predicateB element) head = true := by
                show (predicateA head || predicateB head) = true
                rw [hA, hB]; rfl
              rw [filterConsTrue _ head rest hOr, filterConsFalse predicateA head rest hA,
                  filterConsTrue predicateB head rest hB]
              show (rest.filter (fun element => predicateA element || predicateB element)).length + 1
                  = (rest.filter predicateA).length + ((rest.filter predicateB).length + 1)
              rw [hRec]
              exact Nat.add_assoc _ _ 1
          | false =>
              have hOr : (fun element => predicateA element || predicateB element) head = false := by
                show (predicateA head || predicateB head) = false
                rw [hA, hB]; rfl
              rw [filterConsFalse _ head rest hOr, filterConsFalse predicateA head rest hA,
                  filterConsFalse predicateB head rest hB]
              exact hRec

/-! ### D1 — pair-level append split + the easy reverse direction (block-chain ⟹ union-chain) -/

/-- **The pair-level append split**: `isObstructionPair (edgesA ++ edgesB) a b = isObstructionPair edgesA a
b || isObstructionPair edgesB a b`.  Structural on `edgesA`; the cons step reassociates the `||` by
`Bool.or_assoc`.  The union-at-the-PAIR-level fact (no monochromaticity needed here). -/
theorem isObstructionPairAppendSplit (firstLetter secondLetter : Nat) :
    ∀ (edgesA edgesB : List (Nat × Nat)),
      isObstructionPair (edgesA ++ edgesB) firstLetter secondLetter
        = (isObstructionPair edgesA firstLetter secondLetter
            || isObstructionPair edgesB firstLetter secondLetter)
  | [], edgesB => rfl
  | pair :: remaining, edgesB => by
      show ((natEqBool firstLetter pair.1 && natEqBool secondLetter pair.2)
            || isObstructionPair (remaining ++ edgesB) firstLetter secondLetter)
          = (((natEqBool firstLetter pair.1 && natEqBool secondLetter pair.2)
                || isObstructionPair remaining firstLetter secondLetter)
              || isObstructionPair edgesB firstLetter secondLetter)
      rw [isObstructionPairAppendSplit firstLetter secondLetter remaining edgesB]
      exact (Bool.or_assoc _ _ _).symm

/-- **Left-block chain ⟹ union chain**: an `edgesA`-chain is an `edgesA ++ edgesB`-chain.  Structural on the
word via r13 `guardFirstPair` / `guardTailStep` + `isObstructionPairAppendSplit` + `boolAndIntro`. -/
theorem guardAppendOfLeft (edgesA edgesB : List (Nat × Nat)) :
    ∀ (word : List Nat), allAdjacentPairsAreObstructions edgesA word = true →
      allAdjacentPairsAreObstructions (edgesA ++ edgesB) word = true
  | [], _ => rfl
  | [_], _ => rfl
  | first :: second :: rest, hGuard => by
      have hPair : isObstructionPair edgesA first second = true :=
        guardFirstPair edgesA first second rest hGuard
      have hTail : allAdjacentPairsAreObstructions edgesA (second :: rest) = true :=
        guardTailStep edgesA first (second :: rest) hGuard
      have hRecTail : allAdjacentPairsAreObstructions (edgesA ++ edgesB) (second :: rest) = true :=
        guardAppendOfLeft edgesA edgesB (second :: rest) hTail
      have hPairUnion : isObstructionPair (edgesA ++ edgesB) first second = true := by
        rw [isObstructionPairAppendSplit first second edgesA edgesB, hPair]; rfl
      show (isObstructionPair (edgesA ++ edgesB) first second
              && allAdjacentPairsAreObstructions (edgesA ++ edgesB) (second :: rest)) = true
      exact boolAndIntro hPairUnion hRecTail

/-- **Right-block chain ⟹ union chain**: an `edgesB`-chain is an `edgesA ++ edgesB`-chain (the `Bool.or_true`
twin of `guardAppendOfLeft`). -/
theorem guardAppendOfRight (edgesA edgesB : List (Nat × Nat)) :
    ∀ (word : List Nat), allAdjacentPairsAreObstructions edgesB word = true →
      allAdjacentPairsAreObstructions (edgesA ++ edgesB) word = true
  | [], _ => rfl
  | [_], _ => rfl
  | first :: second :: rest, hGuard => by
      have hPair : isObstructionPair edgesB first second = true :=
        guardFirstPair edgesB first second rest hGuard
      have hTail : allAdjacentPairsAreObstructions edgesB (second :: rest) = true :=
        guardTailStep edgesB first (second :: rest) hGuard
      have hRecTail : allAdjacentPairsAreObstructions (edgesA ++ edgesB) (second :: rest) = true :=
        guardAppendOfRight edgesA edgesB (second :: rest) hTail
      have hPairUnion : isObstructionPair (edgesA ++ edgesB) first second = true := by
        rw [isObstructionPairAppendSplit first second edgesA edgesB, hPair]
        exact Bool.or_true _
      show (isObstructionPair (edgesA ++ edgesB) first second
              && allAdjacentPairsAreObstructions (edgesA ++ edgesB) (second :: rest)) = true
      exact boolAndIntro hPairUnion hRecTail

/-! ### D2 — the forward (hard) monochromaticity: union-chain ⟹ its unique block -/

/-- **Lead-`0` pair forces a `0` successor**: `isObstructionPair unionSystem 0 c = true ==> natEqBool c 0 =
true`.  Reduces `unionSystem = [(0,0),(1,1)]` at lead `0` to `natEqBool c 0 || false`. -/
theorem unionPairLeadZeroForcesZero (secondLetter : Nat)
    (hPair : isObstructionPair unionSystem 0 secondLetter = true) :
    natEqBool secondLetter 0 = true := by
  have hSplit : (natEqBool secondLetter 0 || false) = true := hPair
  cases boolOrElim hSplit with
  | inl hLeft => exact hLeft
  | inr hRight => exact Bool.noConfusion hRight

/-- **Lead-`1` pair forces a `1` successor** (the `yy` twin of `unionPairLeadZeroForcesZero`). -/
theorem unionPairLeadOneForcesOne (secondLetter : Nat)
    (hPair : isObstructionPair unionSystem 1 secondLetter = true) :
    natEqBool secondLetter 1 = true := by
  have hSplit : (natEqBool secondLetter 1 || false) = true := hPair
  cases boolOrElim hSplit with
  | inl hLeft => exact hLeft
  | inr hRight => exact Bool.noConfusion hRight

/-- **A union pair pins its first letter to `0` or `1`**: `isObstructionPair unionSystem a b = true ==>
natEqBool a 0 = true ∨ natEqBool a 1 = true`.  Two nested `boolOrElim` over the `(a=0∧b=0) || (a=1∧b=1)`
structure of `unionSystem`. -/
theorem unionPairFirstLetterCases (firstLetter secondLetter : Nat)
    (hPair : isObstructionPair unionSystem firstLetter secondLetter = true) :
    natEqBool firstLetter 0 = true ∨ natEqBool firstLetter 1 = true := by
  have hSplit : ((natEqBool firstLetter 0 && natEqBool secondLetter 0)
      || ((natEqBool firstLetter 1 && natEqBool secondLetter 1) || false)) = true := hPair
  cases boolOrElim hSplit with
  | inl hLeft => exact Or.inl (boolAndElimLeft hLeft)
  | inr hRight =>
      cases boolOrElim hRight with
      | inl hRightLeft => exact Or.inr (boolAndElimLeft hRightLeft)
      | inr hFalse => exact Bool.noConfusion hFalse

/-- **Lead-`0` propagation**: a lead-`0` union-chain is an `xx`-chain — `guard unionSystem (0 :: rest) = true
==> guard xxSystem (0 :: rest) = true`.  Structural on `rest`: the lead pair forces the next letter to `0`
(`unionPairLeadZeroForcesZero`), then the tail recurses.  Half of the forward monochromaticity. -/
theorem guardXxOfUnionLeadZero :
    ∀ (rest : List Nat), allAdjacentPairsAreObstructions unionSystem (0 :: rest) = true →
      allAdjacentPairsAreObstructions xxSystem (0 :: rest) = true
  | [], _ => rfl
  | secondLetter :: laterRest, hGuard => by
      have hPair : isObstructionPair unionSystem 0 secondLetter = true :=
        guardFirstPair unionSystem 0 secondLetter laterRest hGuard
      have hSecondZero : natEqBool secondLetter 0 = true := unionPairLeadZeroForcesZero secondLetter hPair
      have hSecond : secondLetter = 0 := natEqBoolTrueImpliesEq secondLetter 0 hSecondZero
      have hTailGuard : allAdjacentPairsAreObstructions unionSystem (secondLetter :: laterRest) = true :=
        guardTailStep unionSystem 0 (secondLetter :: laterRest) hGuard
      subst hSecond
      have hRec : allAdjacentPairsAreObstructions xxSystem (0 :: laterRest) = true :=
        guardXxOfUnionLeadZero laterRest hTailGuard
      show (isObstructionPair xxSystem 0 0 && allAdjacentPairsAreObstructions xxSystem (0 :: laterRest)) = true
      exact boolAndIntro rfl hRec

/-- **Lead-`1` propagation**: a lead-`1` union-chain is a `yy`-chain (the `yy` twin of
`guardXxOfUnionLeadZero`). -/
theorem guardYyOfUnionLeadOne :
    ∀ (rest : List Nat), allAdjacentPairsAreObstructions unionSystem (1 :: rest) = true →
      allAdjacentPairsAreObstructions yySystem (1 :: rest) = true
  | [], _ => rfl
  | secondLetter :: laterRest, hGuard => by
      have hPair : isObstructionPair unionSystem 1 secondLetter = true :=
        guardFirstPair unionSystem 1 secondLetter laterRest hGuard
      have hSecondOne : natEqBool secondLetter 1 = true := unionPairLeadOneForcesOne secondLetter hPair
      have hSecond : secondLetter = 1 := natEqBoolTrueImpliesEq secondLetter 1 hSecondOne
      have hTailGuard : allAdjacentPairsAreObstructions unionSystem (secondLetter :: laterRest) = true :=
        guardTailStep unionSystem 1 (secondLetter :: laterRest) hGuard
      subst hSecond
      have hRec : allAdjacentPairsAreObstructions yySystem (1 :: laterRest) = true :=
        guardYyOfUnionLeadOne laterRest hTailGuard
      show (isObstructionPair yySystem 1 1 && allAdjacentPairsAreObstructions yySystem (1 :: laterRest)) = true
      exact boolAndIntro rfl hRec

/-- ★★ **THE FORWARD MONOCHROMATICITY**: a union-chain is a block-chain — `guard unionSystem word = true ==>
guard xxSystem word = true ∨ guard yySystem word = true`.  The lead pair pins the first letter to `0` or `1`
(`unionPairFirstLetterCases`), then the lead-letter propagation (`guardXxOfUnionLeadZero` /
`guardYyOfUnionLeadOne`) carries the whole word into the unique block.  The genuinely-hard leg of the r10
`disjointUnionAdditivityIsNamedNode` skeleton. -/
theorem guardUnionForwardToBlock :
    ∀ (word : List Nat), allAdjacentPairsAreObstructions unionSystem word = true →
      allAdjacentPairsAreObstructions xxSystem word = true
        ∨ allAdjacentPairsAreObstructions yySystem word = true
  | [], _ => Or.inl rfl
  | [_], _ => Or.inl rfl
  | first :: second :: rest, hGuard => by
      have hPair : isObstructionPair unionSystem first second = true :=
        guardFirstPair unionSystem first second rest hGuard
      cases unionPairFirstLetterCases first second hPair with
      | inl hFirstZero =>
          have hFirst : first = 0 := natEqBoolTrueImpliesEq first 0 hFirstZero
          subst hFirst
          exact Or.inl (guardXxOfUnionLeadZero (second :: rest) hGuard)
      | inr hFirstOne =>
          have hFirst : first = 1 := natEqBoolTrueImpliesEq first 1 hFirstOne
          subst hFirst
          exact Or.inr (guardYyOfUnionLeadOne (second :: rest) hGuard)

/-! ### D3 — the pointwise Bool identity, block disjointness, and the additivity headline -/

/-- ★★ **THE POINTWISE BLOCK-`or` IDENTITY**: `guard unionSystem word = guard xxSystem word || guard yySystem
word` for EVERY word.  The `true` case is the forward monochromaticity; the `false` case is the
contrapositive of the reverse containment (`guardAppendOfLeft` / `guardAppendOfRight`, off `unionSystem =
xxSystem ++ yySystem`).  Unconditional — no length hypothesis (the length-`1` boundary is absorbed because
both blocks are trivially true there). -/
theorem guardUnionEqualsBlockOr (word : List Nat) :
    allAdjacentPairsAreObstructions unionSystem word
      = (allAdjacentPairsAreObstructions xxSystem word
          || allAdjacentPairsAreObstructions yySystem word) := by
  cases hUnion : allAdjacentPairsAreObstructions unionSystem word with
  | true =>
      cases guardUnionForwardToBlock word hUnion with
      | inl hxx => rw [hxx]; rfl
      | inr hyy => rw [hyy]; exact (Bool.or_true _).symm
  | false =>
      have hxxFalse : allAdjacentPairsAreObstructions xxSystem word = false := by
        cases hxx : allAdjacentPairsAreObstructions xxSystem word with
        | false => rfl
        | true =>
            have hUnionTrue : allAdjacentPairsAreObstructions unionSystem word = true :=
              guardAppendOfLeft xxSystem yySystem word hxx
            rw [hUnion] at hUnionTrue
            exact Bool.noConfusion hUnionTrue
      have hyyFalse : allAdjacentPairsAreObstructions yySystem word = false := by
        cases hyy : allAdjacentPairsAreObstructions yySystem word with
        | false => rfl
        | true =>
            have hUnionTrue : allAdjacentPairsAreObstructions unionSystem word = true :=
              guardAppendOfRight xxSystem yySystem word hyy
            rw [hUnion] at hUnionTrue
            exact Bool.noConfusion hUnionTrue
      rw [hxxFalse, hyyFalse]; rfl

/-- **An `xx` pair excludes a `yy` pair**: `isObstructionPair xxSystem a b = true ==> isObstructionPair
yySystem a b = false` (an `xx` pair forces `a = 0`, which kills the `yy` pair). -/
theorem xxTrueImpliesYyFalse (firstLetter secondLetter : Nat)
    (hXx : isObstructionPair xxSystem firstLetter secondLetter = true) :
    isObstructionPair yySystem firstLetter secondLetter = false := by
  have hSplit : ((natEqBool firstLetter 0 && natEqBool secondLetter 0) || false) = true := hXx
  have hAnd : (natEqBool firstLetter 0 && natEqBool secondLetter 0) = true := by
    cases boolOrElim hSplit with
    | inl hLeft => exact hLeft
    | inr hRight => exact Bool.noConfusion hRight
  have hFirstZero : natEqBool firstLetter 0 = true := boolAndElimLeft hAnd
  have hFirst : firstLetter = 0 := natEqBoolTrueImpliesEq firstLetter 0 hFirstZero
  subst hFirst
  rfl

/-- **Block disjointness on length-`≥ 2` words**: `guard xxSystem word && guard yySystem word = false` for
any word of length `≥ 2`.  The first pair is either not an `xx` pair (kills `guard xx`) or is, forcing the
`yy` pair false (`xxTrueImpliesYyFalse`, kills `guard yy`).  The disjointness hypothesis of
`filterOrLengthSplit`; length `≥ 2` (degree `≥ 1`) is what excludes the length-`1` double-count. -/
theorem guardBlocksDisjoint : ∀ (word : List Nat), 2 ≤ word.length →
    (allAdjacentPairsAreObstructions xxSystem word
      && allAdjacentPairsAreObstructions yySystem word) = false
  | [], hLen => (Nat.not_succ_le_zero 1 hLen).elim
  | [_], hLen => (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hLen)).elim
  | first :: second :: rest, _ => by
      cases hCase : isObstructionPair xxSystem first second with
      | false =>
          have hGuardXxFalse : allAdjacentPairsAreObstructions xxSystem (first :: second :: rest) = false := by
            show (isObstructionPair xxSystem first second
                    && allAdjacentPairsAreObstructions xxSystem (second :: rest)) = false
            rw [hCase]; rfl
          rw [hGuardXxFalse]; rfl
      | true =>
          have hYyPairFalse : isObstructionPair yySystem first second = false :=
            xxTrueImpliesYyFalse first second hCase
          have hGuardYyFalse : allAdjacentPairsAreObstructions yySystem (first :: second :: rest) = false := by
            show (isObstructionPair yySystem first second
                    && allAdjacentPairsAreObstructions yySystem (second :: rest)) = false
            rw [hYyPairFalse]; rfl
          rw [hGuardYyFalse]
          exact Bool.and_false _

/-- ★★ **THE TWO-BLOCK DISJOINT-UNION ADDITIVITY** (#2145, the r15 T2 headline, the `∀ degree ≥ 1`
delivery): `rank_union degree = rank_xx degree + rank_yy degree` for the letter-disjoint self-loop union
`unionSystem = xxSystem ++ yySystem` over `[0, 1]`, at every degree `≥ 1`.  `filterCongr` swaps the union
guard for `guard_xx || guard_yy` on every candidate (the pointwise identity `guardUnionEqualsBlockOr`), and
`filterOrLengthSplit` splits the length off the block disjointness (`guardBlocksDisjoint`, applicable since
every degree-`degree` candidate has length `degree + 1 ≥ 2`).  This is the `∀ degree ≥ 1` upgrade of r10's
concrete two-block seed `mvListSplitAndAdditivity`; the general k-block additivity over arbitrary
letter-disjoint blocks stays NAMED (`naryDisjointAdditivityGeneralIsNamedNode`). -/
theorem twoBlockDisjointAdditivity : ∀ degree, 1 ≤ degree →
    multiObstructionChainRankOracleOver [0, 1] unionSystem degree
      = multiObstructionChainRankOracleOver [0, 1] xxSystem degree
        + multiObstructionChainRankOracleOver [0, 1] yySystem degree := by
  intro degree hDegree
  show ((allWordsOverAlphabet [0, 1] (degree + 1)).filter
          (allAdjacentPairsAreObstructions unionSystem)).length
      = ((allWordsOverAlphabet [0, 1] (degree + 1)).filter
          (allAdjacentPairsAreObstructions xxSystem)).length
        + ((allWordsOverAlphabet [0, 1] (degree + 1)).filter
            (allAdjacentPairsAreObstructions yySystem)).length
  rw [filterCongr (allAdjacentPairsAreObstructions unionSystem)
        (fun word => allAdjacentPairsAreObstructions xxSystem word
            || allAdjacentPairsAreObstructions yySystem word)
        (allWordsOverAlphabet [0, 1] (degree + 1))
        (fun word _ => guardUnionEqualsBlockOr word)]
  exact filterOrLengthSplit (allAdjacentPairsAreObstructions xxSystem)
      (allAdjacentPairsAreObstructions yySystem)
      (allWordsOverAlphabet [0, 1] (degree + 1))
      (fun word hWord => guardBlocksDisjoint word (by
        have hLenWord : word.length = degree + 1 :=
          memWordsOverAlphabetHasLength [0, 1] (degree + 1) word hWord
        rw [hLenWord]; exact Nat.succ_le_succ hDegree))

/-! ## E — the TOWER-ANICK (#2145 TOWER-TRUNC) r15 ledger + the telescope-wall adjudication (T3) -/

/-- ★ **The TOWER-ANICK (#2145 TOWER-TRUNC) r15 ledger marker.**  What stands, zero-axiom, additively over
r14:

  * **T1 — THE TIGHT SELF-PROPAGATING TRUNCATION** (SHIPPED): `censusPositiveDownwardClosed` (the head-drop
    downward-closure step) + ★★ `censusZeroPropagatesUpward` (once `0`, stays `0` above — STRICTLY tighter
    than r14's loose `alphabet.length`), with `acyclicCensusZeroPropagatesFromAlphabetLength` re-deriving and
    subsuming r14's closed form.  The honest content of #2145's "bounded overlap depth kills the tower above
    the bound".
  * **T2 — THE TWO-BLOCK DISJOINT-UNION ADDITIVITY** (SHIPPED, `∀ degree ≥ 1`): ★★
    `twoBlockDisjointAdditivity`, engined by ★★ `guardUnionEqualsBlockOr` (the pointwise block-`or` identity,
    resting on the forward monochromaticity `guardUnionForwardToBlock`) + ★★ `filterOrLengthSplit` (the
    disjoint-`or` length split) + `guardBlocksDisjoint`.  The `∀ degree ≥ 1` upgrade of r10's concrete
    two-block seed `mvListSplitAndAdditivity`.

HONEST SCOPE — T1 is a statement about the SUPPORT (nonzero-ness), NOT the count: the census sequence is
genuinely NON-MONOTONE (the r15 truth-probe's `3, 4, 6, 8, 12, 16, 24` witness), so no "counts decrease"
claim is made or true.  T2 delivers the self-loop two-block instance only; the general k-block additivity
over arbitrary letter-disjoint blocks stays NAMED (`naryDisjointAdditivityGeneralIsNamedNode`).  The tight
TOPOLOGICAL longest-path bound is SUPERSEDED by T1's self-propagating form (a cleaner route), not delivered.

**T3 — THE TELESCOPE WALL (adjudication-only, NO route, NO flip).**  The general-CONVERGENT telescope
`finiteConvergent ==> H_d` (`generalTelescopeHomologyIsNamedNode`) stays EXPLICITLY WALLED: for a
non-monomial presentation the Anick differential need not vanish under `k ⊗_A` (the cyclic-3 norm augments to
`3 != 0`), so `H_d != C_d` in general — genuine torsion needing the A-module (non-abelianized) Anick
differential and its `Tor(k, k)` exactness (`aModuleAnickDifferentialIsNamedNode` /
`anickResolutionExactnessIsNamedNode` / `normDifferentialFromRelationIsNamedNode`, all standing named nodes).
The T1/T2 monomial track rides the zero boundary `⟨[[0]]⟩`; T3 needs real Smith-form homology over the Fox
differential — no route exists and none is invented here.  No Smith import, no Homology<->Omega edge.  Read
the meaning from THIS docstring (the honest-record convention). -/
def acyclicTruncationDownwardClosureAndBlockAdditivityIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
