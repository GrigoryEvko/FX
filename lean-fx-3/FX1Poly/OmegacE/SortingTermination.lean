import FX1Poly.OmegacE.SortingSystem

/-! # FX1Poly/OmegacE/SortingTermination
    — the inversion-count measure for the sorting system (SN-120 progress 2a, #623)

The bubble-sort termination measure infrastructure.  The sorting system is length-PRESERVING (a swap), so
length is no measure; termination is by the INVERSION COUNT (the number of out-of-order pairs), which strictly
decreases by one per descending swap.

* `countBelowThreshold slotValue threshold` — count the cells whose `slotValue` is strictly below a threshold.
* `countInversions slotValue` — the total inversion count: for each head, the number of later cells with strictly
  smaller slotValue, plus the recursion.
* `crossInversionCount slotValue left right` — the CROSS inversions across an append boundary (each left cell
  pairs with each strictly-smaller right cell); the cross term of the inversion-count append homomorphism.
* `countBelowThreshold_append` + `countInversions_append` — the two monoid homomorphisms from list append to `ℕ`
  addition.  Unlike SN-118's single-cell `aBeforeBInversions` (whose cross term was a product), `countInversions`
  has a SUM-fold cross term `crossInversionCount`, so the append-homomorphism's cons case is a five-term `ℕ` AC
  rearrangement `(a+b)+((c+d)+e) = ((a+c)+d)+(b+e)`, discharged by explicit `Nat.add_assoc` / `Nat.add_left_comm`
  (normalizing both sides to `a+(b+(c+(d+e)))`) — NOT `ac_rfl` (which leaks `propext`+`Quot.sound`).

## Honest scope / deferred

This ships the MEASURE + its two append homomorphisms.  The remaining SN-120 termination atoms (progress 2b):
`countBelowThreshold_preserved_by_step` (a swap preserves the below-threshold count) → cross-term preservation in
both arguments → `countInversions` strictly decreases per step (fire `[a,b]→[b,a]` with `slotValue b < slotValue a`
has inner measure `1 → 0`; context cases split by the homomorphism, cross terms preserved, inner IH) →
`sortingSystem_isTerminating` via `Subrelation` into `InvImage (· < ·) measure`.  Then local confluence (braid
critical pair) + the guarded reducer close SN-120.

## Zero-axiom verification

Verified `#print axioms`-clean in scratch (`countBelowThreshold_append`/`countInversions_append`).  Per-decl gated
in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Count the cells whose `slotValue` is strictly below a threshold. -/
def countBelowThreshold {dimension : Nat} (slotValue : OmegacECell dimension → Nat) (threshold : Nat) :
    List (OmegacECell dimension) → Nat
  | [] => 0
  | head :: tail =>
      (if slotValue head < threshold then 1 else 0) + countBelowThreshold slotValue threshold tail

/-- The inversion count: the number of out-of-order pairs `(i < j)` with `slotValue cellᵢ > slotValue cellⱼ`,
counted as, for each head, the number of later cells with strictly smaller slotValue, plus the recursion.
Strictly decreased by every descending swap — the bubble-sort termination measure. -/
def countInversions {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    List (OmegacECell dimension) → Nat
  | [] => 0
  | head :: tail =>
      countBelowThreshold slotValue (slotValue head) tail + countInversions slotValue tail

/-- The CROSS inversion count across an append boundary: each cell on the left pairs with each strictly-smaller
cell on the right.  The cross term of the inversion-count append homomorphism. -/
def crossInversionCount {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    List (OmegacECell dimension) → List (OmegacECell dimension) → Nat
  | [], _ => 0
  | head :: tail, rightCells =>
      countBelowThreshold slotValue (slotValue head) rightCells
        + crossInversionCount slotValue tail rightCells

/-- `countBelowThreshold` is a monoid homomorphism from list append to `ℕ` addition. -/
theorem countBelowThreshold_append {dimension : Nat} (slotValue : OmegacECell dimension → Nat)
    (threshold : Nat) (leftCells rightCells : List (OmegacECell dimension)) :
    countBelowThreshold slotValue threshold (leftCells ++ rightCells)
      = countBelowThreshold slotValue threshold leftCells
        + countBelowThreshold slotValue threshold rightCells := by
  induction leftCells with
  | nil =>
      show countBelowThreshold slotValue threshold rightCells
        = 0 + countBelowThreshold slotValue threshold rightCells
      rw [Nat.zero_add]
  | cons head tail ih =>
      show (if slotValue head < threshold then 1 else 0)
          + countBelowThreshold slotValue threshold (tail ++ rightCells)
        = ((if slotValue head < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold tail)
          + countBelowThreshold slotValue threshold rightCells
      rw [ih, Nat.add_assoc]

/-- **Inversion count over an append**: the inversions of `left ++ right` are the inversions within `left`,
plus the inversions within `right`, plus the CROSS inversions.  The structural law behind the strict-decrease
proof's context cases. -/
theorem countInversions_append {dimension : Nat} (slotValue : OmegacECell dimension → Nat)
    (leftCells rightCells : List (OmegacECell dimension)) :
    countInversions slotValue (leftCells ++ rightCells)
      = countInversions slotValue leftCells
        + countInversions slotValue rightCells
        + crossInversionCount slotValue leftCells rightCells := by
  induction leftCells with
  | nil =>
      show countInversions slotValue rightCells
        = 0 + countInversions slotValue rightCells + 0
      rw [Nat.zero_add, Nat.add_zero]
  | cons head tail ih =>
      show countBelowThreshold slotValue (slotValue head) (tail ++ rightCells)
          + countInversions slotValue (tail ++ rightCells)
        = (countBelowThreshold slotValue (slotValue head) tail + countInversions slotValue tail)
          + countInversions slotValue rightCells
          + (countBelowThreshold slotValue (slotValue head) rightCells
              + crossInversionCount slotValue tail rightCells)
      rw [countBelowThreshold_append, ih]
      generalize countBelowThreshold slotValue (slotValue head) tail = headBelowLeft
      generalize countBelowThreshold slotValue (slotValue head) rightCells = headBelowRight
      generalize countInversions slotValue tail = invLeft
      generalize countInversions slotValue rightCells = invRight
      generalize crossInversionCount slotValue tail rightCells = crossTerm
      rw [Nat.add_assoc headBelowLeft headBelowRight ((invLeft + invRight) + crossTerm),
          Nat.add_assoc invLeft invRight crossTerm,
          Nat.add_assoc (headBelowLeft + invLeft) invRight (headBelowRight + crossTerm),
          Nat.add_assoc headBelowLeft invLeft (invRight + (headBelowRight + crossTerm)),
          Nat.add_left_comm headBelowRight invLeft (invRight + crossTerm),
          Nat.add_left_comm headBelowRight invRight crossTerm]

end FX1Poly.OmegacE
