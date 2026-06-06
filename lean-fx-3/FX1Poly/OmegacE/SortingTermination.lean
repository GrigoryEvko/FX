import FX1Poly.OmegacE.SortingSystem

/-! # FX1Poly/OmegacE/SortingTermination
    — the inversion-count measure + TERMINATION for the sorting system

The bubble-sort termination measure infrastructure.  The sorting system is length-PRESERVING (a swap), so
length is no measure; termination is by the INVERSION COUNT (the number of out-of-order pairs), which strictly
decreases by one per descending swap.

* `countBelowThreshold slotValue threshold` — count the cells whose `slotValue` is strictly below a threshold.
* `countInversions slotValue` — the total inversion count: for each head, the number of later cells with strictly
  smaller slotValue, plus the recursion.
* `crossInversionCount slotValue left right` — the CROSS inversions across an append boundary (each left cell
  pairs with each strictly-smaller right cell); the cross term of the inversion-count append homomorphism.
* `countBelowThreshold_append` + `countInversions_append` — the two monoid homomorphisms from list append to `ℕ`
  addition.  Unlike the transposition system's single-cell `aBeforeBInversions` (whose cross term is a product), `countInversions`
  has a SUM-fold cross term `crossInversionCount`, so the append-homomorphism's cons case is a five-term `ℕ` AC
  rearrangement `(a+b)+((c+d)+e) = ((a+c)+d)+(b+e)`, discharged by explicit `Nat.add_assoc` / `Nat.add_left_comm`
  (normalizing both sides to `a+(b+(c+(d+e)))`) — NOT `ac_rfl` (which leaks `propext`+`Quot.sound`).

## Termination

* `countBelowThreshold_preserved_by_step` — multiset invariance: a swap preserves the below-threshold count.
* `crossInversionCount_append_left` — additivity of the cross count in its LEFT argument.
* `crossInversionCount_preserved_{right,left}_by_step` — the cross term is preserved in either argument.
* `countInversions_decreases` — the strict per-step decrease (fire `[a,b]→[b,a]` with `slotValue b < slotValue a`
  drops the inner measure `1 → 0`; context cases split by the `countInversions_append` homomorphism, cross terms
  preserved, strict decrease via the inner IH).
* `sortingSystem_isTerminating` — `Subrelation` into `InvImage (· < ·) (countInversions slotValue ·.cells)`.
  CLEANER than `transpositionSystem_isTerminating`: needs NO external `a ≠ b` — the strict-order guard is baked
  into `sortingSystem` membership, so every actual step decreases the measure unconditionally.

## Remaining (separate files)

LOCAL CONFLUENCE with the genuine braid `[a,b,c]` critical pair (multi-step join to the sorted `[c,b,a]`) +
the guarded `WordReducer` (scan for the leftmost descending adjacency) + `decidableConvertibleModulo_ofConvergent`
close the system.

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

/-- **Multiset invariance of the below-threshold count.**  A sorting swap `[a,b] → [b,a]` is a permutation, so
it preserves the number of cells with `slotValue < threshold`, for every threshold.  By induction on the step:
`fire` swaps two opaque indicator terms (closed by `Nat.add_comm` after generalizing them); the context cases
use `countBelowThreshold_append` + the inner IH. -/
theorem countBelowThreshold_preserved_by_step {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) (threshold : Nat)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (sortingSystem slotValue) sourceWord targetWord) :
    countBelowThreshold slotValue threshold sourceWord.cells
      = countBelowThreshold slotValue threshold targetWord.cells := by
  induction step with
  | fire rule isInSystem =>
      obtain ⟨biggerCell, smallerCell, _descending, hrule⟩ := isInSystem
      subst hrule
      show (if slotValue biggerCell < threshold then (1:Nat) else 0)
          + ((if slotValue smallerCell < threshold then (1:Nat) else 0) + 0)
        = (if slotValue smallerCell < threshold then (1:Nat) else 0)
          + ((if slotValue biggerCell < threshold then (1:Nat) else 0) + 0)
      generalize (if slotValue biggerCell < threshold then (1:Nat) else 0) = countBigger
      generalize (if slotValue smallerCell < threshold then (1:Nat) else 0) = countSmaller
      rw [Nat.add_zero, Nat.add_zero]
      exact Nat.add_comm countBigger countSmaller
  | underLeftContext prefixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countBelowThreshold_append, countBelowThreshold_append, innerIH]
  | underRightContext suffixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countBelowThreshold_append, countBelowThreshold_append, innerIH]

/-- `crossInversionCount` is additive in its LEFT argument over append — the structural law behind cross-term
preservation in the left word (mirrors `countBelowThreshold_append`'s shape, recursing on the left list). -/
theorem crossInversionCount_append_left {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (leftA leftB rightCells : List (OmegacECell dimension)) :
    crossInversionCount slotValue (leftA ++ leftB) rightCells
      = crossInversionCount slotValue leftA rightCells
        + crossInversionCount slotValue leftB rightCells := by
  induction leftA with
  | nil =>
      show crossInversionCount slotValue leftB rightCells
        = 0 + crossInversionCount slotValue leftB rightCells
      rw [Nat.zero_add]
  | cons headCell tailCells ih =>
      show countBelowThreshold slotValue (slotValue headCell) rightCells
          + crossInversionCount slotValue (tailCells ++ leftB) rightCells
        = (countBelowThreshold slotValue (slotValue headCell) rightCells
            + crossInversionCount slotValue tailCells rightCells)
          + crossInversionCount slotValue leftB rightCells
      rw [ih, Nat.add_assoc]

/-- **Cross-inversion count preserved by a step in its RIGHT argument.**  The swap permutes the right word's
multiset, and `crossInversionCount left right` depends on `right` only through `countBelowThreshold` (per left
cell), so by induction on `left` + `countBelowThreshold_preserved_by_step` the cross count is unchanged. -/
theorem crossInversionCount_preserved_right_by_step {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) (leftCells : List (OmegacECell dimension))
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (sortingSystem slotValue) sourceWord targetWord) :
    crossInversionCount slotValue leftCells sourceWord.cells
      = crossInversionCount slotValue leftCells targetWord.cells := by
  induction leftCells with
  | nil => rfl
  | cons headCell tailCells ih =>
      show countBelowThreshold slotValue (slotValue headCell) sourceWord.cells
          + crossInversionCount slotValue tailCells sourceWord.cells
        = countBelowThreshold slotValue (slotValue headCell) targetWord.cells
          + crossInversionCount slotValue tailCells targetWord.cells
      rw [countBelowThreshold_preserved_by_step slotValue (slotValue headCell) step, ih]

/-- **Cross-inversion count preserved by a step in its LEFT argument.**  Symmetric to the right-argument case:
induction on the step, `crossInversionCount_append_left` for the context cases, `Nat.add_comm` of two opaque
cross terms for `fire`. -/
theorem crossInversionCount_preserved_left_by_step {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) (rightCells : List (OmegacECell dimension))
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (sortingSystem slotValue) sourceWord targetWord) :
    crossInversionCount slotValue sourceWord.cells rightCells
      = crossInversionCount slotValue targetWord.cells rightCells := by
  induction step with
  | fire rule isInSystem =>
      obtain ⟨biggerCell, smallerCell, _descending, hrule⟩ := isInSystem
      subst hrule
      show countBelowThreshold slotValue (slotValue biggerCell) rightCells
          + (countBelowThreshold slotValue (slotValue smallerCell) rightCells + 0)
        = countBelowThreshold slotValue (slotValue smallerCell) rightCells
          + (countBelowThreshold slotValue (slotValue biggerCell) rightCells + 0)
      generalize countBelowThreshold slotValue (slotValue biggerCell) rightCells = countBigger
      generalize countBelowThreshold slotValue (slotValue smallerCell) rightCells = countSmaller
      rw [Nat.add_zero, Nat.add_zero]
      exact Nat.add_comm countBigger countSmaller
  | underLeftContext prefixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [crossInversionCount_append_left, crossInversionCount_append_left, innerIH]
  | underRightContext suffixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [crossInversionCount_append_left, crossInversionCount_append_left, innerIH]

/-- **The inversion count strictly decreases per sorting swap** — the bubble-sort termination measure.  `fire`
of a guarded swap `[a,b] → [b,a]` with `slotValue b < slotValue a` drops the inner measure `1 → 0` (the `a`-`b`
inversion vanishes; the reverse pair contributes 0 by `<`-asymmetry).  The context cases split via the
`countInversions_append` homomorphism, with the cross term preserved (in the right word for `underLeftContext`,
in the left word for `underRightContext`) and the strict decrease carried by the inner IH. -/
theorem countInversions_decreases {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (sortingSystem slotValue) sourceWord targetWord) :
    countInversions slotValue targetWord.cells < countInversions slotValue sourceWord.cells := by
  induction step with
  | fire rule isInSystem =>
      obtain ⟨biggerCell, smallerCell, descending, hrule⟩ := isInSystem
      subst hrule
      have targetZero : countInversions slotValue [smallerCell, biggerCell] = 0 := by
        show ((if slotValue biggerCell < slotValue smallerCell then (1:Nat) else 0) + 0) + (0 + 0) = 0
        rw [if_neg (Nat.lt_asymm descending)]
      have sourceOne : countInversions slotValue [biggerCell, smallerCell] = 1 := by
        show ((if slotValue smallerCell < slotValue biggerCell then (1:Nat) else 0) + 0) + (0 + 0) = 1
        rw [if_pos descending]
      show countInversions slotValue [smallerCell, biggerCell]
        < countInversions slotValue [biggerCell, smallerCell]
      rw [targetZero, sourceOne]
      exact Nat.zero_lt_one
  | underLeftContext prefixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countInversions_append, countInversions_append,
          ← crossInversionCount_preserved_right_by_step slotValue prefixWord.cells inner]
      exact Nat.add_lt_add_right (Nat.add_lt_add_left innerIH _) _
  | underRightContext suffixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countInversions_append, countInversions_append,
          ← crossInversionCount_preserved_left_by_step slotValue suffixWord.cells inner]
      exact Nat.add_lt_add_right (Nat.add_lt_add_right innerIH _) _

/-- **The sorting system is terminating** — the termination headline.  The inversion measure embeds
reduction into `<` on `ℕ` (well-founded), so every word is accessible.  Unlike `transpositionSystem_isTerminating`
this needs NO external `firstCell ≠ secondCell`: the strict-order guard `slotValue b < slotValue a` is baked into
`sortingSystem` membership, so every actual step strictly decreases the measure unconditionally.  Discharges the
`IsTerminating` premise of `newman` / `decidableConvertibleModulo_ofConvergent` for the sorting presentation. -/
theorem sortingSystem_isTerminating {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    IsTerminating (sortingSystem slotValue) := by
  intro word
  have subrel :
      Subrelation
        (fun reduct source =>
          OmegacEWord.RewritesOneStep (sortingSystem slotValue) source reduct)
        (InvImage (· < ·)
          (fun candidate => countInversions slotValue candidate.cells)) := by
    intro smaller larger hStep
    exact countInversions_decreases slotValue hStep
  exact subrel.accessible
    ((InvImage.wf (fun candidate => countInversions slotValue candidate.cells)
      Nat.lt_wfRel.wf).apply word)

end FX1Poly.OmegacE
