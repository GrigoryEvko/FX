import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisorGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # IntPolynomialSubsetEnumeratorComplete — the k-subset enumerator is complete

`IntPolynomialDeterminantalDivisorGeneral` ships `charDeterminantalDivisor k n M = polyGcdList over
kSubsets`.  Its trustworthiness as a similarity invariant rests on the enumerator `kSublists` missing no
minor: every order-preserving `k`-element sublist of the index list must appear in `kSublists k`, else `d_k`
would be the GCD of a proper subfamily and could be too large.  `kSublistsComplete` closes that gap.

  * `IsOrderedSubset chosen available` — a hand-rolled 3-constructor inductive for the order-preserving
    sublist relation (not `List.Sublist`, whose derived lemmas can pull `propext`).
  * `kSublistsComplete` — `IsOrderedSubset chosen available` implies `chosen ∈ kSublists chosen.length
    available`, by structural recursion on the subset witness: `nil` lands in `kSublists 0 [] = [[]]`;
    `take` lands in the left of the enumerator's `++`; `skip` lands in the right, split on whether the
    chosen sublist is empty or a cons.
  * `kSubsetsComplete` — the corollary for `kSubsets k n = kSublists k (indicesBelow n)`.

The three `List.Mem` construction lemmas are copied locally (prefixed `subsetEnum`) rather than imported, so
the `ComputerAlgebra` layer needs no `Polygraph` dependency; they use the `List.Mem.head`/`List.Mem.tail`
constructors directly, never the `mem_append`/`mem_map` iff-lemmas that leak `propext`.  Structural
induction/recursion over `List.Mem` and `IsOrderedSubset`, plus `decide` groundings.  Free of `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Propext-free list-membership construction kit (local copies) -/

/-- Membership in the left half of an append — copied propext-free from the `Polygraph`
`ExtractionMembership` kit so `ComputerAlgebra` needs no `Polygraph` import.  Structural induction on the
`List.Mem` witness. -/
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

/-- `IsOrderedSubset chosen available` holds when `chosen` is an order-preserving sublist of `available`:
read `available` left to right and at each head either `skip` it or `take` it into `chosen`.  Hand-rolled
(not `List.Sublist`) so every fact proved about it stays `propext`-free. -/
inductive IsOrderedSubset : List Nat → List Nat → Prop
  | nil : IsOrderedSubset [] []
  | skip {chosen : List Nat} {head : Nat} {rest : List Nat} :
      IsOrderedSubset chosen rest → IsOrderedSubset chosen (head :: rest)
  | take {chosen : List Nat} {head : Nat} {rest : List Nat} :
      IsOrderedSubset chosen rest → IsOrderedSubset (head :: chosen) (head :: rest)

/-! ## Completeness of the enumerator -/

/-- **The enumerator misses no order-preserving subset.**  Every `chosen` that is an order-preserving
sublist of `available` appears in `kSublists chosen.length available`.  Structural recursion on the subset
witness: `nil` lands in `kSublists 0 [] = [[]]`; `take head` sits in the left `++` branch (the `map` of
`(head :: ·)`, reached by the induction hypothesis); `skip head` sits in the right branch (the sublists of
`rest` of the same length), split on whether `chosen` is `[]` or a cons.  This is the load-bearing lemma
behind `charDeterminantalDivisor`'s `d_k = GCD over kSubsets`: no `k×k` minor is skipped. -/
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

/-- The completeness corollary for `kSubsets k n = kSublists k (indicesBelow n)`: an order-preserving
subset of the index list `{0, …, n−1}` is enumerated by `kSubsets`. -/
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

/-- Independent `decide` cross-check: the enumerator lists exactly the three `2`-sublists of `[0, 1, 2]`,
with `[0, 2]` the middle one.  Stated as a list equality (not a `List.Mem` decision, whose `Decidable`
instance would pull `propext` / `Quot.sound`), so it stays axiom-free. -/
theorem kSublistsTwoOfZeroOneTwoIsPairs :
    kSublists 2 [0, 1, 2] = [[0, 1], [0, 2], [1, 2]] := by decide

end FX1Poly.ComputerAlgebra
