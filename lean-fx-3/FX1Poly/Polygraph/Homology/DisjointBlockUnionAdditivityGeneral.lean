import FX1Poly.Polygraph.Homology.AcyclicTruncationDownwardClosureAndBlockAdditivity

/-! # FX1Poly/Polygraph/Homology/DisjointBlockUnionAdditivityGeneral — the GENERAL k-block
    disjoint-union census additivity (arbitrary letter-disjoint blocks, `∀ degree ≥ 1`), flipping
    `naryDisjointAdditivityGeneralIsNamedNode` from NAMED to DELIVERED (TOWER-ANICK r16, #2145 TOWER-TRUNC)

r15 `AcyclicTruncationDownwardClosureAndBlockAdditivity` delivered the TWO-BLOCK self-loop instance
`twoBlockDisjointAdditivity` (`∀ degree ≥ 1`), pinned to the literal `unionSystem = [(0,0),(1,1)]` — the
monochromaticity engine `unionPairLeadZeroForcesZero` / `guardXxOfUnionLeadZero` exploits that
`isObstructionPair [(0,0),(1,1)] 0 c` reduces DEFINITIONALLY to `natEqBool c 0 || false`, a residue that
evaporates over an abstract edge-set.  The general k-block additivity over arbitrary letter-disjoint blocks
stayed NAMED (`naryDisjointAdditivityGeneralIsNamedNode`, r12).  This module DELIVERS it, additively over
r15, in two layers:

## G1a — the GENERAL two-block additivity over an abstract separator

`twoBlockAdditivityOverSeparator` (ambient alphabet `A`, disjoint edge-sets `edgesX` / `edgesY`, a Bool
`separator` with `hX`: every `edgesX` pair is separator-`true` on both endpoints, `hY`: every `edgesY` pair
is separator-`false` on both):

  `rank_over A (edgesX ++ edgesY) degree = rank_over A edgesX degree + rank_over A edgesY degree`  (∀ degree ≥ 1)

The r15 GENERIC substrate ports VERBATIM — `filterCongr` / `filterOrLengthSplit` (the disjoint-`or`
length split), `isObstructionPairAppendSplit` / `guardAppendOfLeft` / `guardAppendOfRight` (the pair-level
`||` split + the easy reverse containment, all already quantified over `edgesA edgesB`).  The r15 CONCRETE
monochromaticity layer (the literal-`|| false` reductions) is RE-PROVED separator-driven: the forward
monochromaticity `guardUnionForwardToBlockGeneral` splits each lead pair via `isObstructionPairAppendSplit`
and reads the first letter's separator value from `hX` / `hY` (no literal reduction), then propagates the
whole word into its unique block (`guardEdgesXOfUnionLeadTrue` / `guardEdgesYOfUnionLeadFalse`).  Block
disjointness `guardBlocksDisjointGeneral` rests on `edgesXPairExcludesEdgesYPair` (an `edgesX` pair forces
separator-`true`, killing any `edgesY` pair by `hY`'s separator-`false`).  r15's
`twoBlockDisjointAdditivity` returns as a one-line corollary `twoBlockDisjointAdditivityViaSeparator`
(separator `natListContains [0]`, ambient `[0,1]`) — a free regression cross-check.

## G1b — the k-block additivity by List induction

`kBlockAdditivity` folds `twoBlockAdditivityOverSeparator` over a `List UnionBlock` with the ambient
alphabet FIXED throughout (the truth-probe confirmed a block census over its own alphabet equals its census
over the enlarged union alphabet at degree ≥ 1, so no alphabet-shrink lemma is needed):

  `rank_over A (blocks.flatMap edges) degree = Σ_{blk ∈ blocks} rank_over A blk.edges degree`  (∀ degree ≥ 1)

Peeling `head :: rest` uses `separator := natListContains head.alphabet`; `hX` is the head's block-locality,
`hY` is the ONE genuinely-new k-block leg `restPairSeparatorFalse` — every pair of `rest.flatMap edges`
avoids the head alphabet, proved by induction over `rest` via `isObstructionPairAppendSplit` + per-block
locality + pairwise alphabet disjointness.  The base case `blocks = []` is
`emptyEdgesCensusZeroAtPositiveDegree` (a length-≥2 word fails the empty guard `false && _`, so the census
is `0` at every degree ≥ 1).

## Necessity of block-locality (the cross-edge negative control)

The r16 truth-probe measured, over the 3-block 2-cycle union `{0,1}/{3,4}/{6,7}` with ONE crossing edge
`(1,3)` added, `union = 7, 8, 9, 10` against `sum = 6, 6, 6, 6` at degrees 1..4 — additivity BROKEN.  The
block-locality hypotheses (`hX`/`hY`, equivalently pairwise alphabet disjointness) are therefore NECESSARY,
not decoration: the theorem is FALSE without them.

## Literature anchor (the printed decomposition this specializes)

A letter-disjoint union of monomial obstruction systems is the free product (coproduct) of the associated
monomial algebras.  The per-degree chain-count additivity (degree ≥ 1) is the monomial specialization of
the printed coproduct Tor/Ext decomposition — Le Meur, "Cohomology of products and coproducts of augmented
algebras," arXiv:1007.4110, Theorem 4.1: the coproduct resolution of `k` is `P∗↑ ⊕ Q∗↑` "in degrees
greater than zero," with degree 0 the sole exception ("In degree zero both sides equal k").  Graph-side
(Leymarie–Musson, arXiv:2307.06144): the unique start node `C₀ = {1}` is shared by every block, counted
once truthfully but k times blockwise — exactly the degree-0 −(k−1) collision the `1 ≤ degree` gate
excludes.  In the monomial / zero-boundary regime the Anick differential vanishes, so census = Tor rank =
Betti number and the additivity is an EQUALITY; beyond monomial (non-vanishing convergent Anick
differential) census ≥ Betti and the combinatorial additivity becomes only an upper bound — the telescope
wall (see the ledger).

## Zero-axiom design decisions (the lane's propext minefield)

  * The pair-level union split is `isObstructionPairAppendSplit` (r15, generic in `edgesA edgesB`) — it,
    NOT any literal `|| false` reduction, carries every block split, so the proof is alphabet-agnostic.
  * Separator agreement is by `Bool.noConfusion` on `separator first = true` vs `= false` — never
    `Bool.and_eq_true` / `Bool.or_eq_true` (both leak `propext`); the `||` split is r13 `boolOrElim`, the
    `&&` build r13 `boolAndIntro`.
  * Pairwise alphabet disjointness `pairwiseDisjointAlphabets` is a STRUCTURAL `Prop`-recursion on the
    block list (`.1` / `.2` project by defeq); the empty-edges guard-false and the `flatMap` cons split are
    definitional (`(blk :: rest).flatMap edges = blk.edges ++ rest.flatMap edges`).
  * The `2 ≤ word.length` gate flows from `memWordsOverAlphabetHasLength` + `Nat.succ_le_succ` (additive,
    never `Nat.sub`); the length-case eliminations use `Nat.not_succ_le_zero` / `Nat.le_of_succ_le_succ`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (word / edge / block lists, `Nat.le` witness).  Per-declaration gated (and independently
`#print axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/DisjointBlockUnionAdditivityGeneral.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## A — the separator-driven forward monochromaticity (the RE-PROVED concrete layer) -/

/-- **Lead-`true` propagation into `edgesX`**: with `separator firstLetter = true`, a `(edgesX ++ edgesY)`
chain led by `firstLetter` is an `edgesX` chain.  Structural on `rest`: the lead pair splits via
`isObstructionPairAppendSplit`; the `edgesY` branch is killed by `hY` (it would force `separator firstLetter
= false`), so the pair is an `edgesX` pair and `hX` propagates `separator = true` to the next letter, where
the tail recurses.  The separator-driven analog of r15's `guardXxOfUnionLeadZero`. -/
theorem guardEdgesXOfUnionLeadTrue (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false) :
    ∀ (firstLetter : Nat) (rest : List Nat), separator firstLetter = true →
      allAdjacentPairsAreObstructions (edgesX ++ edgesY) (firstLetter :: rest) = true →
      allAdjacentPairsAreObstructions edgesX (firstLetter :: rest) = true
  | _, [], _, _ => rfl
  | firstLetter, secondLetter :: laterRest, hSepFirst, hGuard => by
      have hPairUnion : isObstructionPair (edgesX ++ edgesY) firstLetter secondLetter = true :=
        guardFirstPair (edgesX ++ edgesY) firstLetter secondLetter laterRest hGuard
      have hSplit : (isObstructionPair edgesX firstLetter secondLetter
                      || isObstructionPair edgesY firstLetter secondLetter) = true := by
        rw [← isObstructionPairAppendSplit firstLetter secondLetter edgesX edgesY]; exact hPairUnion
      have hPairX : isObstructionPair edgesX firstLetter secondLetter = true := by
        cases boolOrElim hSplit with
        | inl hInX => exact hInX
        | inr hInY =>
            have hSepFalse : separator firstLetter = false := (hY firstLetter secondLetter hInY).1
            rw [hSepFirst] at hSepFalse
            exact Bool.noConfusion hSepFalse
      have hSepSecond : separator secondLetter = true := (hX firstLetter secondLetter hPairX).2
      have hTailGuard : allAdjacentPairsAreObstructions (edgesX ++ edgesY) (secondLetter :: laterRest) = true :=
        guardTailStep (edgesX ++ edgesY) firstLetter (secondLetter :: laterRest) hGuard
      have hRec : allAdjacentPairsAreObstructions edgesX (secondLetter :: laterRest) = true :=
        guardEdgesXOfUnionLeadTrue edgesX edgesY separator hX hY secondLetter laterRest hSepSecond hTailGuard
      show (isObstructionPair edgesX firstLetter secondLetter
              && allAdjacentPairsAreObstructions edgesX (secondLetter :: laterRest)) = true
      exact boolAndIntro hPairX hRec

/-- **Lead-`false` propagation into `edgesY`** (the mirror of `guardEdgesXOfUnionLeadTrue`): with `separator
firstLetter = false`, a `(edgesX ++ edgesY)` chain led by `firstLetter` is an `edgesY` chain.  The `edgesX`
branch is killed by `hX` (it would force `separator firstLetter = true`). -/
theorem guardEdgesYOfUnionLeadFalse (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false) :
    ∀ (firstLetter : Nat) (rest : List Nat), separator firstLetter = false →
      allAdjacentPairsAreObstructions (edgesX ++ edgesY) (firstLetter :: rest) = true →
      allAdjacentPairsAreObstructions edgesY (firstLetter :: rest) = true
  | _, [], _, _ => rfl
  | firstLetter, secondLetter :: laterRest, hSepFirst, hGuard => by
      have hPairUnion : isObstructionPair (edgesX ++ edgesY) firstLetter secondLetter = true :=
        guardFirstPair (edgesX ++ edgesY) firstLetter secondLetter laterRest hGuard
      have hSplit : (isObstructionPair edgesX firstLetter secondLetter
                      || isObstructionPair edgesY firstLetter secondLetter) = true := by
        rw [← isObstructionPairAppendSplit firstLetter secondLetter edgesX edgesY]; exact hPairUnion
      have hPairY : isObstructionPair edgesY firstLetter secondLetter = true := by
        cases boolOrElim hSplit with
        | inl hInX =>
            have hSepTrue : separator firstLetter = true := (hX firstLetter secondLetter hInX).1
            rw [hSepFirst] at hSepTrue
            exact Bool.noConfusion hSepTrue
        | inr hInY => exact hInY
      have hSepSecond : separator secondLetter = false := (hY firstLetter secondLetter hPairY).2
      have hTailGuard : allAdjacentPairsAreObstructions (edgesX ++ edgesY) (secondLetter :: laterRest) = true :=
        guardTailStep (edgesX ++ edgesY) firstLetter (secondLetter :: laterRest) hGuard
      have hRec : allAdjacentPairsAreObstructions edgesY (secondLetter :: laterRest) = true :=
        guardEdgesYOfUnionLeadFalse edgesX edgesY separator hX hY secondLetter laterRest hSepSecond hTailGuard
      show (isObstructionPair edgesY firstLetter secondLetter
              && allAdjacentPairsAreObstructions edgesY (secondLetter :: laterRest)) = true
      exact boolAndIntro hPairY hRec

/-- ★★ **THE GENERAL FORWARD MONOCHROMATICITY**: a `(edgesX ++ edgesY)` chain is a chain of its unique
block.  The lead pair pins the first letter's separator value (via `isObstructionPairAppendSplit` + `hX` /
`hY`), and the lead-value propagation carries the whole word into `edgesX` (separator-`true`) or `edgesY`
(separator-`false`).  The separator-driven analog of r15's `guardUnionForwardToBlock`. -/
theorem guardUnionForwardToBlockGeneral (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false) :
    ∀ (word : List Nat), allAdjacentPairsAreObstructions (edgesX ++ edgesY) word = true →
      allAdjacentPairsAreObstructions edgesX word = true
        ∨ allAdjacentPairsAreObstructions edgesY word = true
  | [], _ => Or.inl rfl
  | [_], _ => Or.inl rfl
  | firstLetter :: secondLetter :: rest, hGuard => by
      have hPairUnion : isObstructionPair (edgesX ++ edgesY) firstLetter secondLetter = true :=
        guardFirstPair (edgesX ++ edgesY) firstLetter secondLetter rest hGuard
      have hSplit : (isObstructionPair edgesX firstLetter secondLetter
                      || isObstructionPair edgesY firstLetter secondLetter) = true := by
        rw [← isObstructionPairAppendSplit firstLetter secondLetter edgesX edgesY]; exact hPairUnion
      cases boolOrElim hSplit with
      | inl hInX =>
          have hSepFirst : separator firstLetter = true := (hX firstLetter secondLetter hInX).1
          exact Or.inl (guardEdgesXOfUnionLeadTrue edgesX edgesY separator hX hY firstLetter
            (secondLetter :: rest) hSepFirst hGuard)
      | inr hInY =>
          have hSepFirst : separator firstLetter = false := (hY firstLetter secondLetter hInY).1
          exact Or.inr (guardEdgesYOfUnionLeadFalse edgesX edgesY separator hX hY firstLetter
            (secondLetter :: rest) hSepFirst hGuard)

/-! ## B — the pointwise Bool identity, pair-exclusion, and block disjointness -/

/-- ★★ **THE GENERAL POINTWISE BLOCK-`or` IDENTITY**: `guard (edgesX ++ edgesY) word = guard edgesX word ||
guard edgesY word` for EVERY word.  The `true` case is `guardUnionForwardToBlockGeneral`; the `false` case
is the contrapositive of the reverse containment `guardAppendOfLeft` / `guardAppendOfRight` (r15, generic in
the edge-sets — ported verbatim).  Unconditional (no length hypothesis), so `filterCongr` accepts it. -/
theorem guardUnionEqualsBlockOrGeneral (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false)
    (word : List Nat) :
    allAdjacentPairsAreObstructions (edgesX ++ edgesY) word
      = (allAdjacentPairsAreObstructions edgesX word
          || allAdjacentPairsAreObstructions edgesY word) := by
  cases hUnion : allAdjacentPairsAreObstructions (edgesX ++ edgesY) word with
  | true =>
      cases guardUnionForwardToBlockGeneral edgesX edgesY separator hX hY word hUnion with
      | inl hInX => rw [hInX]; rfl
      | inr hInY => rw [hInY]; exact (Bool.or_true _).symm
  | false =>
      have hXfalse : allAdjacentPairsAreObstructions edgesX word = false := by
        cases hCase : allAdjacentPairsAreObstructions edgesX word with
        | false => rfl
        | true =>
            have hUnionTrue : allAdjacentPairsAreObstructions (edgesX ++ edgesY) word = true :=
              guardAppendOfLeft edgesX edgesY word hCase
            rw [hUnion] at hUnionTrue
            exact Bool.noConfusion hUnionTrue
      have hYfalse : allAdjacentPairsAreObstructions edgesY word = false := by
        cases hCase : allAdjacentPairsAreObstructions edgesY word with
        | false => rfl
        | true =>
            have hUnionTrue : allAdjacentPairsAreObstructions (edgesX ++ edgesY) word = true :=
              guardAppendOfRight edgesX edgesY word hCase
            rw [hUnion] at hUnionTrue
            exact Bool.noConfusion hUnionTrue
      rw [hXfalse, hYfalse]; rfl

/-- **An `edgesX` pair excludes an `edgesY` pair**: `isObstructionPair edgesX a b = true ==>
isObstructionPair edgesY a b = false`.  An `edgesX` pair forces `separator a = true` (`hX`); an `edgesY`
pair would force `separator a = false` (`hY`), a `Bool.noConfusion` clash. -/
theorem edgesXPairExcludesEdgesYPair (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false)
    (firstLetter secondLetter : Nat)
    (hXpair : isObstructionPair edgesX firstLetter secondLetter = true) :
    isObstructionPair edgesY firstLetter secondLetter = false := by
  cases hCase : isObstructionPair edgesY firstLetter secondLetter with
  | false => rfl
  | true =>
      have hSepTrue : separator firstLetter = true := (hX firstLetter secondLetter hXpair).1
      have hSepFalse : separator firstLetter = false := (hY firstLetter secondLetter hCase).1
      rw [hSepTrue] at hSepFalse
      exact Bool.noConfusion hSepFalse

/-- ★★ **GENERAL BLOCK DISJOINTNESS on length-`≥ 2` words**: `guard edgesX word && guard edgesY word =
false` for any word of length `≥ 2`.  The first pair is either not an `edgesX` pair (kills `guard edgesX`)
or is, forcing the `edgesY` pair false (`edgesXPairExcludesEdgesYPair`, kills `guard edgesY`).  The
disjointness hypothesis of `filterOrLengthSplit`.  The separator-driven analog of r15's
`guardBlocksDisjoint`. -/
theorem guardBlocksDisjointGeneral (edgesX edgesY : List (Nat × Nat)) (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false) :
    ∀ (word : List Nat), 2 ≤ word.length →
      (allAdjacentPairsAreObstructions edgesX word
        && allAdjacentPairsAreObstructions edgesY word) = false
  | [], hLen => (Nat.not_succ_le_zero 1 hLen).elim
  | [_], hLen => (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hLen)).elim
  | firstLetter :: secondLetter :: rest, _ => by
      cases hCase : isObstructionPair edgesX firstLetter secondLetter with
      | false =>
          have hGuardXFalse :
              allAdjacentPairsAreObstructions edgesX (firstLetter :: secondLetter :: rest) = false := by
            show (isObstructionPair edgesX firstLetter secondLetter
                    && allAdjacentPairsAreObstructions edgesX (secondLetter :: rest)) = false
            rw [hCase]; rfl
          rw [hGuardXFalse]; rfl
      | true =>
          have hYPairFalse : isObstructionPair edgesY firstLetter secondLetter = false :=
            edgesXPairExcludesEdgesYPair edgesX edgesY separator hX hY firstLetter secondLetter hCase
          have hGuardYFalse :
              allAdjacentPairsAreObstructions edgesY (firstLetter :: secondLetter :: rest) = false := by
            show (isObstructionPair edgesY firstLetter secondLetter
                    && allAdjacentPairsAreObstructions edgesY (secondLetter :: rest)) = false
            rw [hYPairFalse]; rfl
          rw [hGuardYFalse]; exact Bool.and_false _

/-! ## C — the GENERAL two-block additivity + the r15 recovery corollary (G1a) -/

/-- ★★ **THE GENERAL TWO-BLOCK DISJOINT-UNION ADDITIVITY**: over any ambient alphabet, for disjoint
edge-sets `edgesX` / `edgesY` separated by a Bool `separator` (`hX` / `hY` place each block's pairs on the
`true` / `false` side), `rank_over ambient (edgesX ++ edgesY) degree = rank_over ambient edgesX degree +
rank_over ambient edgesY degree` at every degree `≥ 1`.  `filterCongr` swaps the union guard for `guard
edgesX || guard edgesY` (`guardUnionEqualsBlockOrGeneral`); `filterOrLengthSplit` splits the length off the
block disjointness (`guardBlocksDisjointGeneral`, applicable since every degree-`degree` candidate has
length `degree + 1 ≥ 2`).  The alphabet-agnostic upgrade of r15's `twoBlockDisjointAdditivity`. -/
theorem twoBlockAdditivityOverSeparator (ambient : List Nat) (edgesX edgesY : List (Nat × Nat))
    (separator : Nat → Bool)
    (hX : ∀ firstLetter secondLetter,
      isObstructionPair edgesX firstLetter secondLetter = true →
      separator firstLetter = true ∧ separator secondLetter = true)
    (hY : ∀ firstLetter secondLetter,
      isObstructionPair edgesY firstLetter secondLetter = true →
      separator firstLetter = false ∧ separator secondLetter = false) :
    ∀ degree, 1 ≤ degree →
      multiObstructionChainRankOracleOver ambient (edgesX ++ edgesY) degree
        = multiObstructionChainRankOracleOver ambient edgesX degree
          + multiObstructionChainRankOracleOver ambient edgesY degree := by
  intro degree hDegree
  show ((allWordsOverAlphabet ambient (degree + 1)).filter
          (allAdjacentPairsAreObstructions (edgesX ++ edgesY))).length
      = ((allWordsOverAlphabet ambient (degree + 1)).filter
          (allAdjacentPairsAreObstructions edgesX)).length
        + ((allWordsOverAlphabet ambient (degree + 1)).filter
            (allAdjacentPairsAreObstructions edgesY)).length
  rw [filterCongr (allAdjacentPairsAreObstructions (edgesX ++ edgesY))
        (fun word => allAdjacentPairsAreObstructions edgesX word
            || allAdjacentPairsAreObstructions edgesY word)
        (allWordsOverAlphabet ambient (degree + 1))
        (fun word _ => guardUnionEqualsBlockOrGeneral edgesX edgesY separator hX hY word)]
  exact filterOrLengthSplit (allAdjacentPairsAreObstructions edgesX)
      (allAdjacentPairsAreObstructions edgesY)
      (allWordsOverAlphabet ambient (degree + 1))
      (fun word hWord => guardBlocksDisjointGeneral edgesX edgesY separator hX hY word (by
        have hLenWord : word.length = degree + 1 :=
          memWordsOverAlphabetHasLength ambient (degree + 1) word hWord
        rw [hLenWord]; exact Nat.succ_le_succ hDegree))

/-- **A self-loop pair forces both endpoints to the loop letter**: `isObstructionPair [(loopLetter,
loopLetter)] a b = true ==> a = loopLetter ∧ b = loopLetter`.  Reduces `[(v, v)]` to `(natEqBool a v &&
natEqBool b v) || false`. -/
theorem selfLoopPairForcesEq (loopLetter firstLetter secondLetter : Nat)
    (hPair : isObstructionPair [(loopLetter, loopLetter)] firstLetter secondLetter = true) :
    firstLetter = loopLetter ∧ secondLetter = loopLetter := by
  have hSplit : ((natEqBool firstLetter loopLetter && natEqBool secondLetter loopLetter) || false) = true :=
    hPair
  have hAnd : (natEqBool firstLetter loopLetter && natEqBool secondLetter loopLetter) = true := by
    cases boolOrElim hSplit with
    | inl hLeft => exact hLeft
    | inr hRight => exact Bool.noConfusion hRight
  exact ⟨natEqBoolTrueImpliesEq firstLetter loopLetter (boolAndElimLeft hAnd),
         natEqBoolTrueImpliesEq secondLetter loopLetter (boolAndElimRight hAnd)⟩

/-- ★ **r15's `twoBlockDisjointAdditivity` RECOVERED as a corollary** (free regression cross-check): the
literal self-loop two-block union `unionSystem = xxSystem ++ yySystem = [(0,0),(1,1)]` over `[0,1]` is the
`twoBlockAdditivityOverSeparator` instance at separator `natListContains [0]` — the `xx` block sits on the
separator-`true` side (`a = 0`), the `yy` block on the separator-`false` side (`a = 1`). -/
theorem twoBlockDisjointAdditivityViaSeparator : ∀ degree, 1 ≤ degree →
    multiObstructionChainRankOracleOver [0, 1] unionSystem degree
      = multiObstructionChainRankOracleOver [0, 1] xxSystem degree
        + multiObstructionChainRankOracleOver [0, 1] yySystem degree := by
  have hX : ∀ firstLetter secondLetter,
      isObstructionPair xxSystem firstLetter secondLetter = true →
      natListContains [0] firstLetter = true ∧ natListContains [0] secondLetter = true := by
    intro firstLetter secondLetter hPair
    obtain ⟨hFirst, hSecond⟩ := selfLoopPairForcesEq 0 firstLetter secondLetter hPair
    subst hFirst; subst hSecond
    exact ⟨rfl, rfl⟩
  have hY : ∀ firstLetter secondLetter,
      isObstructionPair yySystem firstLetter secondLetter = true →
      natListContains [0] firstLetter = false ∧ natListContains [0] secondLetter = false := by
    intro firstLetter secondLetter hPair
    obtain ⟨hFirst, hSecond⟩ := selfLoopPairForcesEq 1 firstLetter secondLetter hPair
    subst hFirst; subst hSecond
    exact ⟨rfl, rfl⟩
  exact twoBlockAdditivityOverSeparator [0, 1] xxSystem yySystem (natListContains [0]) hX hY

/-! ## D — the k-block layer (List induction over the blocks) (G1b) -/

/-- A union block: its alphabet (the letters it owns) and its obstruction edge-set. -/
structure UnionBlock where
  /-- The letters this block owns (pairwise-disjoint from every other block's alphabet). -/
  alphabet : List Nat
  /-- This block's obstruction edge-set (local to its own alphabet). -/
  edges : List (Nat × Nat)

/-- The sum of a per-block measure over a block list.  Structural fold. -/
def sumOverBlocks (measure : UnionBlock → Nat) : List UnionBlock → Nat
  | [] => 0
  | head :: rest => measure head + sumOverBlocks measure rest

/-- **One-directional alphabet disjointness**: every letter of `alphabetA` is absent from `alphabetB`. -/
def alphabetDisjoint (alphabetA alphabetB : List Nat) : Prop :=
  ∀ letter, natListContains alphabetA letter = true → natListContains alphabetB letter = false

/-- **Pairwise alphabet disjointness of a block list**: each block's alphabet is disjoint from every LATER
block's alphabet.  Structural `Prop`-recursion (`.1` / `.2` project by defeq — no `propext`). -/
def pairwiseDisjointAlphabets : List UnionBlock → Prop
  | [] => True
  | head :: rest =>
      (∀ laterBlock, laterBlock ∈ rest → alphabetDisjoint laterBlock.alphabet head.alphabet)
        ∧ pairwiseDisjointAlphabets rest

/-- **The empty guard is false on a length-`≥ 2` word**: `allAdjacentPairsAreObstructions [] word = false`
whenever `2 ≤ word.length` (the first pair reduces `isObstructionPair [] _ _` to `false`, so `false && _ =
false`).  Length-case elimination like `guardBlocksDisjointGeneral`. -/
theorem emptyEdgesGuardFalseOnLongWord : ∀ (word : List Nat), 2 ≤ word.length →
    allAdjacentPairsAreObstructions [] word = false
  | [], hLen => (Nat.not_succ_le_zero 1 hLen).elim
  | [_], hLen => (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hLen)).elim
  | _ :: _ :: _, _ => rfl

/-- **The empty-edge census vanishes at positive degree**: `rank_over ambient [] degree = 0` for degree `≥
1`.  Every degree-`degree` candidate has length `degree + 1 ≥ 2`, so the empty guard is false on all of them
(`emptyEdgesGuardFalseOnLongWord`) and the chain filter empties (`filterAllFalseIsNil`).  The k-block base
case. -/
theorem emptyEdgesCensusZeroAtPositiveDegree (ambient : List Nat) (degree : Nat) (hDegree : 1 ≤ degree) :
    multiObstructionChainRankOracleOver ambient [] degree = 0 := by
  have hChainsEmpty : multiObstructionChainsAtDegreeOver ambient [] degree = [] := by
    show (allWordsOverAlphabet ambient (degree + 1)).filter (allAdjacentPairsAreObstructions []) = []
    apply filterAllFalseIsNil
    intro word hWordMem
    have hLenWord : word.length = degree + 1 :=
      memWordsOverAlphabetHasLength ambient (degree + 1) word hWordMem
    have hTwoLe : 2 ≤ word.length := by rw [hLenWord]; exact Nat.succ_le_succ hDegree
    exact emptyEdgesGuardFalseOnLongWord word hTwoLe
  show (multiObstructionChainsAtDegreeOver ambient [] degree).length = 0
  rw [hChainsEmpty]
  rfl

/-- ★★ **THE REST-PAIR SEPARATOR LEG** (the one genuinely-new k-block ingredient): every pair of
`rest.flatMap edges` avoids the head alphabet — `isObstructionPair (rest.flatMap edges) a b = true ==>
natListContains headAlphabet a = false ∧ natListContains headAlphabet b = false`, under per-block locality
(each rest block's pairs stay in its own alphabet) and pairwise disjointness (each rest block's alphabet is
disjoint from the head alphabet).  Structural on `rest`: the base `[]` gives `isObstructionPair [] a b =
false` (`Bool.noConfusion`); the cons splits the flatMap `(blk :: rest').flatMap edges = blk.edges ++
rest'.flatMap edges` via `isObstructionPairAppendSplit`, discharging the `blk` branch through locality +
disjointness and recursing on the rest. -/
theorem restPairSeparatorFalse (headAlphabet : List Nat) :
    ∀ (blocks : List UnionBlock),
      (∀ blk, blk ∈ blocks → ∀ firstLetter secondLetter,
        isObstructionPair blk.edges firstLetter secondLetter = true →
        natListContains blk.alphabet firstLetter = true
          ∧ natListContains blk.alphabet secondLetter = true) →
      (∀ blk, blk ∈ blocks → alphabetDisjoint blk.alphabet headAlphabet) →
      ∀ firstLetter secondLetter,
        isObstructionPair (blocks.flatMap (fun blk => blk.edges)) firstLetter secondLetter = true →
        natListContains headAlphabet firstLetter = false
          ∧ natListContains headAlphabet secondLetter = false
  | [], _, _, firstLetter, secondLetter, hPair => by
      have hEmpty : isObstructionPair ([] : List (Nat × Nat)) firstLetter secondLetter = true := hPair
      exact Bool.noConfusion hEmpty
  | blk :: rest, hLocality, hDisjoint, firstLetter, secondLetter, hPair => by
      have hSplit : (isObstructionPair blk.edges firstLetter secondLetter
                      || isObstructionPair (rest.flatMap (fun laterBlock => laterBlock.edges))
                            firstLetter secondLetter) = true := by
        rw [← isObstructionPairAppendSplit firstLetter secondLetter blk.edges
              (rest.flatMap (fun laterBlock => laterBlock.edges))]
        exact hPair
      cases boolOrElim hSplit with
      | inl hInBlk =>
          obtain ⟨hFirstInBlk, hSecondInBlk⟩ :=
            hLocality blk (List.Mem.head rest) firstLetter secondLetter hInBlk
          exact ⟨hDisjoint blk (List.Mem.head rest) firstLetter hFirstInBlk,
                 hDisjoint blk (List.Mem.head rest) secondLetter hSecondInBlk⟩
      | inr hInRest =>
          exact restPairSeparatorFalse headAlphabet rest
            (fun laterBlock hLater => hLocality laterBlock (List.Mem.tail blk hLater))
            (fun laterBlock hLater => hDisjoint laterBlock (List.Mem.tail blk hLater))
            firstLetter secondLetter hInRest

/-- ★★ **THE GENERAL k-BLOCK DISJOINT-UNION ADDITIVITY** (#2145, the r16 headline — flips
`naryDisjointAdditivityGeneralIsNamedNode` to DELIVERED): for a `List UnionBlock` with block-locality (each
block's pairs stay in its own alphabet) and pairwise alphabet disjointness, `rank_over ambient
(blocks.flatMap edges) degree = Σ_{blk} rank_over ambient blk.edges degree` at every degree `≥ 1`.  List
induction over the blocks with the ambient alphabet FIXED: peel `head :: rest`, take `separator :=
natListContains head.alphabet`, apply `twoBlockAdditivityOverSeparator` (`hX` = head locality, `hY` =
`restPairSeparatorFalse`), and recurse on `rest`.  Base case `blocks = []` is
`emptyEdgesCensusZeroAtPositiveDegree`.  Block-locality is NECESSARY (the r16 cross-edge negative control
breaks additivity without it). -/
theorem kBlockAdditivity (ambient : List Nat) (degree : Nat) (hDegree : 1 ≤ degree) :
    ∀ (blocks : List UnionBlock),
      (∀ blk, blk ∈ blocks → ∀ firstLetter secondLetter,
        isObstructionPair blk.edges firstLetter secondLetter = true →
        natListContains blk.alphabet firstLetter = true
          ∧ natListContains blk.alphabet secondLetter = true) →
      pairwiseDisjointAlphabets blocks →
      multiObstructionChainRankOracleOver ambient (blocks.flatMap (fun blk => blk.edges)) degree
        = sumOverBlocks (fun blk => multiObstructionChainRankOracleOver ambient blk.edges degree) blocks
  | [], _, _ => by
      show multiObstructionChainRankOracleOver ambient [] degree = 0
      exact emptyEdgesCensusZeroAtPositiveDegree ambient degree hDegree
  | head :: rest, hLocality, hDisjoint => by
      have hHeadLocality : ∀ firstLetter secondLetter,
          isObstructionPair head.edges firstLetter secondLetter = true →
          natListContains head.alphabet firstLetter = true
            ∧ natListContains head.alphabet secondLetter = true :=
        hLocality head (List.Mem.head rest)
      have hRestLocality : ∀ blk, blk ∈ rest → ∀ firstLetter secondLetter,
          isObstructionPair blk.edges firstLetter secondLetter = true →
          natListContains blk.alphabet firstLetter = true
            ∧ natListContains blk.alphabet secondLetter = true :=
        fun blk hBlk => hLocality blk (List.Mem.tail head hBlk)
      have hRestDisjoint : ∀ blk, blk ∈ rest → alphabetDisjoint blk.alphabet head.alphabet :=
        hDisjoint.1
      have hY : ∀ firstLetter secondLetter,
          isObstructionPair (rest.flatMap (fun blk => blk.edges)) firstLetter secondLetter = true →
          natListContains head.alphabet firstLetter = false
            ∧ natListContains head.alphabet secondLetter = false :=
        restPairSeparatorFalse head.alphabet rest hRestLocality hRestDisjoint
      have hTwoBlock :
          multiObstructionChainRankOracleOver ambient
              (head.edges ++ rest.flatMap (fun blk => blk.edges)) degree
            = multiObstructionChainRankOracleOver ambient head.edges degree
              + multiObstructionChainRankOracleOver ambient
                  (rest.flatMap (fun blk => blk.edges)) degree :=
        twoBlockAdditivityOverSeparator ambient head.edges (rest.flatMap (fun blk => blk.edges))
          (natListContains head.alphabet) hHeadLocality hY degree hDegree
      have hRec :
          multiObstructionChainRankOracleOver ambient (rest.flatMap (fun blk => blk.edges)) degree
            = sumOverBlocks (fun blk => multiObstructionChainRankOracleOver ambient blk.edges degree) rest :=
        kBlockAdditivity ambient degree hDegree rest hRestLocality hDisjoint.2
      show multiObstructionChainRankOracleOver ambient
            (head.edges ++ rest.flatMap (fun blk => blk.edges)) degree
          = multiObstructionChainRankOracleOver ambient head.edges degree
            + sumOverBlocks (fun blk => multiObstructionChainRankOracleOver ambient blk.edges degree) rest
      rw [hTwoBlock, hRec]

/-! ## E — end-to-end non-vacuity witness (the general theorem FIRES on a k=3 fixture) -/

/-- A self-loop block on `loopLetter`: alphabet `[loopLetter]`, edge-set `[(loopLetter, loopLetter)]`. -/
def selfLoopBlock (loopLetter : Nat) : UnionBlock :=
  { alphabet := [loopLetter], edges := [(loopLetter, loopLetter)] }

/-- Locality of a self-loop block: its only pair is `(loopLetter, loopLetter)`, both endpoints in
`[loopLetter]`. -/
theorem selfLoopBlockLocality (loopLetter : Nat) :
    ∀ firstLetter secondLetter,
      isObstructionPair (selfLoopBlock loopLetter).edges firstLetter secondLetter = true →
      natListContains (selfLoopBlock loopLetter).alphabet firstLetter = true
        ∧ natListContains (selfLoopBlock loopLetter).alphabet secondLetter = true := by
  intro firstLetter secondLetter hPair
  obtain ⟨hFirst, hSecond⟩ := selfLoopPairForcesEq loopLetter firstLetter secondLetter hPair
  rw [hFirst, hSecond]
  refine ⟨?_, ?_⟩
  · show (natEqBool loopLetter loopLetter || natListContains [] loopLetter) = true
    rw [natEqBoolRefl loopLetter]; rfl
  · show (natEqBool loopLetter loopLetter || natListContains [] loopLetter) = true
    rw [natEqBoolRefl loopLetter]; rfl

/-- A `[distinctLetter]` alphabet is disjoint from `[loopLetter]` when the letters differ: membership in
`[distinctLetter]` forces the queried letter to be `distinctLetter`, which then misses `[loopLetter]`. -/
theorem singletonAlphabetDisjoint (loopLetter distinctLetter : Nat)
    (hMiss : natListContains [loopLetter] distinctLetter = false) :
    alphabetDisjoint [distinctLetter] [loopLetter] := by
  intro letter hLetter
  have hEqDistinct : natEqBool distinctLetter letter = true := by
    have hSplit : (natEqBool distinctLetter letter || natListContains [] letter) = true := hLetter
    cases boolOrElim hSplit with
    | inl hLeft => exact hLeft
    | inr hRight => exact Bool.noConfusion hRight
  have hLetterEq : distinctLetter = letter := natEqBoolTrueImpliesEq distinctLetter letter hEqDistinct
  rw [← hLetterEq]; exact hMiss

/-- ★ **THE k=3 END-TO-END WITNESS** (the general theorem is not vacuous): three self-loop blocks on the
distinct letters `0` / `1` / `2` over the ambient alphabet `[0,1,2]` satisfy `kBlockAdditivity` — the union
census equals the sum of the three block censuses at every degree `≥ 1`.  Both the per-block locality and
the pairwise alphabet disjointness are discharged from `selfLoopBlockLocality` /
`singletonAlphabetDisjoint`; the numerical values (`3 = 1 + 1 + 1`) are r12's `naryDisjointUnionCensus`. -/
theorem threeSelfLoopBlockAdditivity : ∀ degree, 1 ≤ degree →
    multiObstructionChainRankOracleOver [0, 1, 2]
        ([selfLoopBlock 0, selfLoopBlock 1, selfLoopBlock 2].flatMap (fun blk => blk.edges)) degree
      = sumOverBlocks
          (fun blk => multiObstructionChainRankOracleOver [0, 1, 2] blk.edges degree)
          [selfLoopBlock 0, selfLoopBlock 1, selfLoopBlock 2] := by
  intro degree hDegree
  refine kBlockAdditivity [0, 1, 2] degree hDegree
    [selfLoopBlock 0, selfLoopBlock 1, selfLoopBlock 2] ?_ ?_
  · intro blk hBlk
    cases hBlk with
    | head => exact selfLoopBlockLocality 0
    | tail _ hRest1 =>
        cases hRest1 with
        | head => exact selfLoopBlockLocality 1
        | tail _ hRest2 =>
            cases hRest2 with
            | head => exact selfLoopBlockLocality 2
            | tail _ hEmpty => cases hEmpty
  · refine ⟨?_, ?_, ?_, True.intro⟩
    · intro laterBlock hLater
      cases hLater with
      | head => exact singletonAlphabetDisjoint 0 1 rfl
      | tail _ hRest =>
          cases hRest with
          | head => exact singletonAlphabetDisjoint 0 2 rfl
          | tail _ hEmpty => cases hEmpty
    · intro laterBlock hLater
      cases hLater with
      | head => exact singletonAlphabetDisjoint 1 2 rfl
      | tail _ hEmpty => cases hEmpty
    · intro laterBlock hLater
      cases hLater

/-! ## F — the TOWER-ANICK (#2145 TOWER-TRUNC) r16 ledger + the lane-resting adjudication (G2) -/

/-- ★ **The TOWER-ANICK (#2145 TOWER-TRUNC) r16 ledger marker.**  What stands, zero-axiom, additively over
r15 — the honest PER-NODE census of the disjoint-union additivity leg, with the resting call stated
explicitly:

## DELIVERED (this round, r16)

  * ★★ **`naryDisjointAdditivityGeneralIsNamedNode` — FLIPPED NAMED → DELIVERED.**  The general k-block
    disjoint-union additivity over ARBITRARY letter-disjoint blocks, `∀ degree ≥ 1`:
      * `twoBlockAdditivityOverSeparator` — the general two-block additivity over an abstract Bool
        `separator` (ambient alphabet, disjoint edge-sets), re-proving r15's concrete literal-`|| false`
        monochromaticity as separator-driven (`guardUnionForwardToBlockGeneral` via
        `isObstructionPairAppendSplit`), porting the r15 GENERIC substrate (`filterCongr` /
        `filterOrLengthSplit` / the append-split / the reverse containment) VERBATIM.
      * `kBlockAdditivity` — the List-induction fold to k blocks, ambient alphabet FIXED, `hY` the one
        genuinely-new leg `restPairSeparatorFalse`, base case `emptyEdgesCensusZeroAtPositiveDegree`.
      * `twoBlockDisjointAdditivityViaSeparator` — r15's `twoBlockDisjointAdditivity` recovered as a
        one-line corollary (separator `natListContains [0]`, ambient `[0,1]`), a free regression.
      * `threeSelfLoopBlockAdditivity` — the k=3 end-to-end non-vacuity witness (three self-loops on
        `0`/`1`/`2`, both locality and disjointness discharged).

## STANDING WALLS (NAMED, never papered)

  * **`generalTelescopeHomologyIsNamedNode` (T3, the telescope wall)** — EXPLICITLY WALLED, NO route, NO
    flip.  For a non-monomial presentation the Anick differential need not vanish under `k ⊗_A` (the
    cyclic-3 norm augments to `3 ≠ 0`), so `H_d ≠ C_d` in general — genuine `Tor(k,k)` torsion needing the
    A-module (non-abelianized) Anick differential and its exactness
    (`aModuleAnickDifferentialIsNamedNode` / `anickResolutionExactnessIsNamedNode` /
    `normDifferentialFromRelationIsNamedNode`, all standing).  LITERATURE-ANCHORED (Le Meur, arXiv:1007.4110
    Thm 4.1): the abstract coproduct Tor split holds in all degrees > 0, but census (chain count) EQUALS
    Betti (homology rank) ONLY where the differential is zero (the monomial track); with a non-vanishing
    convergent differential census ≥ Betti, so the combinatorial additivity ceases to compute homology and
    becomes only an upper bound.  r16 does NOT touch T3.
  * The tight TOPOLOGICAL longest-path bound — SUPERSEDED by r15's T1 self-propagating truncation
    (`censusZeroPropagatesUpward`), not separately delivered.
  * No Smith import, no Homology<->Omega edge (lane law).

## THE RESTING ADJUDICATION (stated explicitly)

r16 FLIPS `naryDisjointAdditivityGeneralIsNamedNode` from NAMED to DELIVERED — the general k-block
disjoint-union additivity (∀ degree ≥ 1, arbitrary letter-disjoint blocks, block-locality NECESSARY per the
cross-edge negative control) via `twoBlockAdditivityOverSeparator` + List-induction `kBlockAdditivity`,
recovering r15's `twoBlockDisjointAdditivity` as a corollary.  The monomial-model additivity leg of #2145
TOWER-TRUNC now RESTS: with r15's tight self-propagating truncation (T1) and r16's general disjoint-union
additivity (T2 generalized), the monomial (zero-boundary) census layer is closed to the degree the
Ufnarovski graph-of-chains supports.  The telescope wall T3 (`generalTelescopeHomologyIsNamedNode`) stays
EXPLICITLY WALLED — census = homology only where the Anick differential is zero; the general convergent
differential is the unresolved frontier, and NO route is invented here.  Read the meaning from THIS
docstring (the honest-record convention). -/
def disjointBlockUnionAdditivityGeneralIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
