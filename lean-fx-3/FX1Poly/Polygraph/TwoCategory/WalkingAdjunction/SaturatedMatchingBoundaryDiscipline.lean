import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingEmptyBoundary

/-! # mode-3 — the saturated soundness re-gated on the boundary discipline

The saturated soundness chain (`saturatedConv_matchingOf_eq` and its `…_of_commute` /
`…_of_swapRenameable` sharpenings) discharges the `ofFull` interchange case through the
UNCONDITIONAL state-parametric `godementInvariant` — the residual the arc route REFUTED as
stated (`not_matchingGodementSwapRenameable`: a non-fresh state lets a cup allocate a colliding
id).  The MODE3-B campaign closed the correct, CONDITIONED form instead:
`matchingOf_sound_ofCupCapCells_allBoundaries` proves the `ofFull` conclusion outright for
cup/cap-disciplined cells at every source boundary, with all conditions seeded by construction.

This file re-gates the saturated chain on that PROVEN leg:

  * `cellHasCupCapGenerators_ofAdjunctionSignature` — the discipline is UNIVERSAL over the
    walking adjunction: its only generators are the unit (`0 ⇒ 2` cup) and the counit
    (`2 ⇒ 0` cap), so EVERY cell satisfies `CellHasCupCapGenerators` by structural recursion;
  * ★ `saturatedConv_matchingOf_eq_ofBoundaryDiscipline` — the saturated soundness with the
    `ofFull` case discharged by the MODE3-B capstone (no `godementInvariant`, no
    `MatchingGodementCommute`, no renaming-witness hypothesis).  The ONLY remaining soundness
    input is the four-field compositionality `MatchingSaturatedCongruence`;
  * `saturatedMatchingCanonicalization_ofBoundaryDiscipline` — the keystone assembled from
    just the congruence and a `convOfMapEq` reconstruction (MODE3-D).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The cup/cap discipline is universal over the walking adjunction.**  Its only 2-cell
generators are the unit (`nil ⇒ leftThenRight`, a `0 ⇒ 2` cup) and the counit
(`rightThenLeft ⇒ nil`, a `2 ⇒ 0` cap), so every cell satisfies `CellHasCupCapGenerators`
by structural recursion — identities are vacuous, composites and whiskerings recurse. -/
theorem cellHasCupCapGenerators_ofAdjunctionSignature :
    {sourceMode targetMode : AdjunctionMode} →
    {localDom localCod : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature localDom localCod) →
    CellHasCupCapGenerators cell
  | _, _, _, _, .gen generator => by
      cases generator with
      | unit => exact Or.inl ⟨rfl, rfl⟩
      | counit => exact Or.inr ⟨rfl, rfl⟩
  | _, _, _, _, .id _ => True.intro
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      ⟨cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha,
        cellHasCupCapGenerators_ofAdjunctionSignature cellBeta⟩
  | _, _, _, _, .whiskerLeft _ body => cellHasCupCapGenerators_ofAdjunctionSignature body
  | _, _, _, _, .whiskerRight _ body => cellHasCupCapGenerators_ofAdjunctionSignature body

/-- ★ **The saturated soundness, re-gated on the boundary discipline.**  `matchingOf` is
invariant under the COMPLETE `SaturatedTwoCellConv` given ONLY the four-field congruence
compositionality: the `ofFull` interchange case is discharged by the PROVEN
`matchingOf_sound_ofCupCapCells_allBoundaries` (every walking-adjunction cell is cup/cap-
disciplined), the triangles are on-the-nose, `whiskerExchange` is same-spine, and the
congruences consume the four fields.  The unconditional `godementInvariant` /
`MatchingGodementCommute` / renaming-witness hypotheses are GONE from the chain. -/
theorem saturatedConv_matchingOf_eq_ofBoundaryDiscipline
    (congruence : MatchingSaturatedCongruence)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB := by
  induction conv with
  | ofFull convFull =>
      exact matchingOf_sound_ofCupCapCells_allBoundaries
        (cellHasCupCapGenerators_ofAdjunctionSignature _) convFull
  | triangleLeft => exact matchingOf_triangleLeft
  | triangleRight => exact matchingOf_triangleRight
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      exact congruence.vcompLeft cellBeta inductionHypothesis
  | vcompCongrRight cellAlpha _ inductionHypothesis =>
      exact congruence.vcompRight cellAlpha inductionHypothesis
  | whiskerLeftCongr oneCell _ inductionHypothesis =>
      exact congruence.whiskerLeft oneCell inductionHypothesis
  | whiskerRightCongr oneCell _ inductionHypothesis =>
      exact congruence.whiskerRight oneCell inductionHypothesis
  | whiskerExchange leftWhisker rightWhisker body =>
      exact matchingOf_whiskerExchange leftWhisker rightWhisker body
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- ★ **The keystone assembled from the boundary-disciplined soundness.**  A
`SaturatedMatchingCanonicalization` is determined by the four-field congruence and a
`convOfMapEq` reconstruction alone — the Godement soundness residual is CLOSED (consumed
through the MODE3-B capstone), not hypothesized. -/
def saturatedMatchingCanonicalization_ofBoundaryDiscipline
    (congruence : MatchingSaturatedCongruence)
    (convOfMapEq : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
      matchingOf cellA = matchingOf cellB → SaturatedTwoCellConv cellA cellB) :
    SaturatedMatchingCanonicalization where
  mapEqOfConv := fun conv => saturatedConv_matchingOf_eq_ofBoundaryDiscipline congruence conv
  convOfMapEq := convOfMapEq

/-! ## Honesty marker -/

/-- **Honesty marker — the saturated soundness is RE-GATED on the boundary discipline.**
`saturatedConv_matchingOf_eq_ofBoundaryDiscipline` proves the complete saturated soundness
with the `ofFull` interchange case discharged by the PROVEN MODE3-B capstone
(`matchingOf_sound_ofCupCapCells_allBoundaries`, applicable because
`cellHasCupCapGenerators_ofAdjunctionSignature` makes the discipline universal over the
walking adjunction).  The unconditional `godementInvariant` / `MatchingGodementCommute` /
renaming-witness inputs are ELIMINATED from the saturated chain — the remaining soundness
residual is EXACTLY the four-field `MatchingSaturatedCongruence` (MODE3-C), and the keystone
additionally needs `convOfMapEq` (MODE3-D).  `= true`. -/
def fxMode_hasSaturatedSoundnessOnBoundaryDiscipline : Bool := true

end FX1Poly.Polygraph
