import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisorGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialSubsetEnumeratorComplete —
the `k`-subset enumerator is COMPLETE (WP-ENDO #2255 follow-on brick)

`IntPolynomialDeterminantalDivisorGeneral` ships the general-`n` determinantal-divisor
engine `charDeterminantalDivisor k n M = polyGcdList over kSubsets`.  Its trustworthiness as
a similarity *invariant* rests on the enumerator `kSublists` MISSING NO minor: every
order-preserving `k`-element sublist of the index list must actually appear in
`kSublists k`.  If the enumerator dropped one subset, `d_k` would be the GCD of a proper
subfamily of the `k×k` minors and could be too large — a silent soundness hole.  This file
closes that gap.

## Contents

  * `IsOrderedSubset chosen available` — a hand-rolled 3-constructor inductive for the
    order-preserving sublist relation (`nil`; `skip` the head of `available`; `take` the
    shared head into `chosen`).  We do NOT reuse `List.Sublist`, whose derived
    characterization lemmas can pull `propext`.
  * `kSublistsComplete` — ★ the completeness theorem: `IsOrderedSubset chosen available`
    implies `chosen ∈ kSublists chosen.length available`, by structural recursion on the
    subset witness.  `nil` lands as the sole `[]` of `kSublists 0 [] = [[]]`; `take` lands in
    the LEFT of the enumerator's `++` (the "took the head" branch, hit through the `List.map`
    lemma); `skip` lands in the RIGHT (the "skipped the head" branch), splitting on whether
    the chosen sublist is empty (length `0`, the `[[]]` base) or a cons (the `++` is then
    exposed and the induction hypothesis lands on the right).
  * `kSubsetsComplete` — the corollary specialised to
    `kSubsets k n = kSublists k (indicesBelow n)`.
  * concrete groundings: the witness `IsOrderedSubset [0,2] [0,1,2]`, its enumeration through
    the completeness theorem, and an independent `decide` cross-check that the two agree.

## Propext-free membership kit (copied locally)

To keep the `ComputerAlgebra` layer free of any `Polygraph` dependency, the three `List.Mem`
construction lemmas are COPIED here (prefixed `subsetEnum`) rather than imported.  They
reason with the `List.Mem.head` / `List.Mem.tail` constructors directly — never the
`List.mem_append` / `List.mem_map` iff-lemmas, which leak `propext`.  Originals:
`Polygraph/TwoCategory/FreeTwoCell/ExtractionMembership.lean` (`listMemAppendOfLeft`,
`listMemAppendOfRight`) and `SwapSuccessorEnumeration.lean` (`listMemMapOfMem`).

## Zero-axiom design

Structural induction/recursion over `List.Mem` and `IsOrderedSubset` (the enumerator's first
argument reduces cleanly because `List.length` is structural, so `(head :: chosen).length`
is definitionally `chosen.length + 1`), plus `decide` groundings.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
`#print axioms` clean; gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Propext-free list-membership construction kit (local copies) -/

/-- Membership in the left half of an append — copied propext-free from the `Polygraph`
`ExtractionMembership` kit so `ComputerAlgebra` needs no `Polygraph` import.  Structural
induction on the `List.Mem` witness. -/
theorem subsetEnumMemAppendOfLeft {elementType : Type} {element : elementType}
    {frontList : List elementType} (backList : List elementType)
    (elementMem : element ∈ frontList) : element ∈ frontList ++ backList := by
  induction elementMem with
  | head remaining => exact List.Mem.head (remaining ++ backList)
  | tail headElement _ innerHypothesis => exact List.Mem.tail headElement innerHypothesis

/-- Membership in the right half of an append — copied propext-free from the `Polygraph`
`ExtractionMembership` kit.  Structural recursion on the front list. -/
theorem subsetEnumMemAppendOfRight {elementType : Type} {element : elementType}
    {backList : List elementType} :
    (frontList : List elementType) → element ∈ backList → element ∈ frontList ++ backList
  | [], elementMem => elementMem
  | headElement :: remaining, elementMem =>
      List.Mem.tail headElement (subsetEnumMemAppendOfRight remaining elementMem)

/-- Membership transported through `List.map` — copied propext-free from the `Polygraph`
`SwapSuccessorEnumeration` kit.  Structural induction on the `List.Mem` witness. -/
theorem subsetEnumMemMapOfMem {sourceType targetType : Type}
    {transform : sourceType → targetType} {element : sourceType}
    {inputList : List sourceType} (elementMem : element ∈ inputList) :
    transform element ∈ inputList.map transform := by
  induction elementMem with
  | head remaining => exact List.Mem.head _
  | tail headElement _ innerHypothesis => exact List.Mem.tail _ innerHypothesis

/-! ## The order-preserving subset relation -/

/-- `IsOrderedSubset chosen available` holds when `chosen` is an order-preserving sublist of
`available`: read `available` left to right and at each head either `skip` it or `take` it
into `chosen`.  Hand-rolled (not `List.Sublist`) so every fact proved about it stays
`propext`-free. -/
inductive IsOrderedSubset : List Nat → List Nat → Prop
  | nil : IsOrderedSubset [] []
  | skip {chosen : List Nat} {head : Nat} {rest : List Nat} :
      IsOrderedSubset chosen rest → IsOrderedSubset chosen (head :: rest)
  | take {chosen : List Nat} {head : Nat} {rest : List Nat} :
      IsOrderedSubset chosen rest → IsOrderedSubset (head :: chosen) (head :: rest)

/-! ## Completeness of the enumerator -/

/-- ★ **The enumerator misses no order-preserving subset.**  Every `chosen` that is an
order-preserving sublist of `available` appears in `kSublists chosen.length available`.
Structural recursion on the subset witness:

  * `nil`: `[]` is the unique length-`0` sublist and `kSublists 0 [] = [[]]` lists it;
  * `take head`: `head :: chosen` sits in the LEFT `++` branch — the `map` of `(head :: ·)`
    over the length-`chosen.length` sublists of `rest`, reached by the induction hypothesis;
  * `skip head`: `chosen` sits in the RIGHT `++` branch — the sublists of `rest` of the SAME
    length — split on whether `chosen` is `[]` (the `[[]]` base of `kSublists 0`) or a cons
    (then the `++` is exposed and the induction hypothesis lands on the right).

This is the load-bearing lemma behind `charDeterminantalDivisor`'s `d_k = GCD over kSubsets`:
no `k×k` minor of the characteristic matrix is skipped, so the general determinantal divisor
is the GCD of the FULL minor family, not a proper subfamily. -/
theorem kSublistsComplete {chosen available : List Nat}
    (subset : IsOrderedSubset chosen available) :
    chosen ∈ kSublists chosen.length available := by
  induction subset with
  | nil => exact List.Mem.head _
  | @skip chosen head rest _subPremise innerHypothesis =>
      cases chosen with
      | nil => exact List.Mem.head _
      | cons _chosenHead chosenRest =>
          exact subsetEnumMemAppendOfRight _ innerHypothesis
  | @take chosen head rest _subPremise innerHypothesis =>
      exact subsetEnumMemAppendOfLeft _ (subsetEnumMemMapOfMem innerHypothesis)

/-- The completeness corollary for `kSubsets k n = kSublists k (indicesBelow n)`: an
order-preserving subset of the index list `{0, …, n−1}` is enumerated by `kSubsets`. -/
theorem kSubsetsComplete {chosen : List Nat} {dimension : Nat}
    (subset : IsOrderedSubset chosen (indicesBelow dimension)) :
    chosen ∈ kSubsets chosen.length dimension :=
  kSublistsComplete subset

/-! ## Concrete groundings -/

/-- `[0, 2]` is an order-preserving sublist of `[0, 1, 2]`: take `0`, skip `1`, take `2`. -/
theorem orderedSubsetZeroTwo : IsOrderedSubset [0, 2] [0, 1, 2] :=
  .take (.skip (.take .nil))

/-- Through `kSublistsComplete`, that witness lands `[0, 2]` inside `kSublists 2 [0, 1, 2]`
(`[0, 2].length = 2` definitionally). -/
theorem orderedSubsetZeroTwoIsEnumerated : [0, 2] ∈ kSublists 2 [0, 1, 2] :=
  kSublistsComplete orderedSubsetZeroTwo

/-- Independent `decide` cross-check: the enumerator lists exactly the three `2`-sublists of
`[0, 1, 2]`, with `[0, 2]` the middle one — agreeing with the proof-term route above.  Stated
as a list EQUALITY (not a `List.Mem` decision, whose `Decidable` instance would pull
`propext` / `Quot.sound`), so it stays axiom-free like the sibling groundings. -/
theorem kSublistsTwoOfZeroOneTwoIsPairs :
    kSublists 2 [0, 1, 2] = [[0, 1], [0, 2], [1, 2]] := by decide

/-! ## The marker -/

/-- ★ **The `k`-subset enumerator is proved complete.**  `= true` records that
`kSublistsComplete` closes the "proved completeness of the enumerator (order-preserving
subset ⟹ enumerated)" follow-on named in `IntPolynomialDeterminantalDivisorGeneral`: the
general determinantal-divisor engine's `d_k = GCD over kSubsets` provably skips no `k×k`
minor of the characteristic matrix. -/
def fxIntPoly_hasSubsetEnumeratorCompleteness : Bool := true

end FX1Poly.ComputerAlgebra
