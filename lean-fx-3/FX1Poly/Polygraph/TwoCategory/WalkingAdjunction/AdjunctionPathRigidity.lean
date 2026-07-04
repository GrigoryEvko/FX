import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # AdjunctionPathRigidity — seed 1-cells are length-determined (SAT-ARC-REC brick ARC-1)

The walking-adjunction quiver has exactly ONE modality out of each mode (`left : base ⟶ tip`,
`right : tip ⟶ base`), so a 1-cell path is completely determined by its source mode and its
LENGTH.  This is the rigidity that closes the arc fold's right-context blindness on CHAINED
spines: the arc structure records only lengths, but at the seed, lengths + the running boundary
pin the actual paths — so chained atoms are determined by their arc read-offs.

  * `adjunctionModality_unique` — parallel seed modalities are equal (each hom is a
    subsingleton);
  * `adjunctionPathTargets_eq_of_length_eq` — two seed paths from ONE source with equal lengths
    land on the SAME mode (the heterogeneous rigidity — the form atom-determination consumes);
  * ★ `adjunctionPath_eq_of_length_eq` — two parallel seed paths with equal lengths are EQUAL.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Parallel seed modalities are equal: each hom of the adjunction quiver is a subsingleton
(`left` is the only `base ⟶ tip`, `right` the only `tip ⟶ base`). -/
theorem adjunctionModality_unique {sourceMode targetMode : AdjunctionMode}
    (firstModality secondModality : AdjunctionModality sourceMode targetMode) :
    firstModality = secondModality := by
  cases firstModality with
  | left => cases secondModality with | left => rfl
  | right => cases secondModality with | right => rfl

/-- **Heterogeneous rigidity**: two seed paths out of the SAME source mode with equal lengths
land on the same target mode — from each mode there is exactly one outgoing modality, so the
mode sequence is a function of (source, length). -/
theorem adjunctionPathTargets_eq_of_length_eq :
    ∀ {sourceMode targetA targetB : adjunctionGraph.Mode}
      (firstPath : ModalityPath adjunctionGraph sourceMode targetA)
      (secondPath : ModalityPath adjunctionGraph sourceMode targetB),
      firstPath.length = secondPath.length → targetA = targetB := by
  intro sourceMode targetA targetB firstPath
  induction firstPath with
  | nil startMode =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => rfl
      | cons secondModality secondRest => nomatch lengthsEqual
  | cons firstModality firstRest inductionHypothesis =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => nomatch lengthsEqual
      | cons secondModality secondRest =>
          cases firstModality with
          | left =>
              cases secondModality with
              | left => exact inductionHypothesis secondRest (Nat.succ.inj lengthsEqual)
          | right =>
              cases secondModality with
              | right => exact inductionHypothesis secondRest (Nat.succ.inj lengthsEqual)

/-- ★ **Seed path rigidity**: two PARALLEL walking-adjunction 1-cells with equal lengths are
equal.  Induction on the first path; at each step the outgoing modality is unique
(`adjunctionModality_unique` content, realized by the double `cases`), so the paths agree
head-by-head. -/
theorem adjunctionPath_eq_of_length_eq :
    ∀ {sourceMode targetMode : adjunctionGraph.Mode}
      (firstPath secondPath : ModalityPath adjunctionGraph sourceMode targetMode),
      firstPath.length = secondPath.length → firstPath = secondPath := by
  intro sourceMode targetMode firstPath
  induction firstPath with
  | nil startMode =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => rfl
      | cons secondModality secondRest => nomatch lengthsEqual
  | cons firstModality firstRest inductionHypothesis =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => nomatch lengthsEqual
      | cons secondModality secondRest =>
          cases firstModality with
          | left =>
              cases secondModality with
              | left =>
                  rw [inductionHypothesis secondRest (Nat.succ.inj lengthsEqual)]
          | right =>
              cases secondModality with
              | right =>
                  rw [inductionHypothesis secondRest (Nat.succ.inj lengthsEqual)]

/-! ## Honesty marker -/

/-- **Honesty marker — seed path rigidity is SHIPPED.**  Walking-adjunction 1-cells are
determined by (source mode, length): `adjunctionPath_eq_of_length_eq` (parallel form) +
`adjunctionPathTargets_eq_of_length_eq` (heterogeneous form).  This is ARC-1 of the
cell-reconstruction ladder: the arc fold reads atoms only through LENGTHS
(`stepArcAtom`'s right-context blindness, refuted for raw lists at
`not_arcHeadExtractionMatching`), and rigidity is what makes lengths + the chained running
boundary DETERMINE seed atoms — the correction that moves head extraction to the
boundary-chained fragment.  NOT yet shipped: the chained-atom determination corollary and the
chained head extraction itself (ARC-2), the chained matching assembly (ARC-3), and the seed
`ArcCellReconstruction` instance (ARC-4, the `fxMode_hasArcCellReconstruction` flip).
`= true`. -/
def fxMode_hasAdjunctionPathRigidity : Bool := true

end FX1Poly.Polygraph
