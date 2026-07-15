-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarUnitLawRefutation

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarUnitalRestatement — the completeness target re-stated over
the UNITAL scope: the four (co)unit laws restored (WP-PROP r30, #2033)

★★ **THE CORRECTED-CORRECTED TARGET.**  The r30 sibling refuted the r29 star through the missing (co)unit
laws.  This file restores them: `BunchedBimonoidUnitCounitRow` carries the four honest unitor rows (left/right
unit, left/right counit — each MATRIX-SOUND, machine-checked `rfl`), the star scope widens by them, and the
completeness target is re-stated over the widened (Lafont) scope.  Three honesty fires:

  * the exact r30 refutation pair IS convertible over the unital scope (a one-row fire) — the correction
    closes precisely the exposed hole;
  * the counit-side pair fires too;
  * the affine-offset separation is DEAD against the unital scope: the new rows relate cells with DIFFERENT
    augmented values (machine-checked), so the r30 refutation invariant cannot re-fire — the unital siege is
    genuinely open, not trivially re-refutable by the same absorber.

The unital owner `fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen = false` opens the honest siege:
the completeness bill (total retract via the r29-delivered block-threading + the r8 `wideSwap` riffle gate +
the r26 recComb perm middle + assembly) now runs against a scope that can actually cancel units.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE FOUR (CO)UNIT ROWS
    # =========================================================================================
-/

/-- The left-unit-law left leg `(eta_a |> a) ; mu_a : id.a => a`. -/
def bunchedBimonoidLeftUnitLawLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidAdditiveGen)
    bunchedBimonoidAddMuGen

/-- The left-counit-law left leg `delta_a ; (eps_a |> a) : a => id.a`. -/
def bunchedBimonoidLeftCounitLawLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddDeltaGen
    (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen)

/-- ★★ **The four (co)unit rows** — the honest unitor laws the r2 excision dropped: each relates the
unit/counit composite to the identity strand.  Each row is matrix-sound (`rfl`, below). -/
inductive BunchedBimonoidUnitCounitRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d →
      Prop where
  /-- Right unit `(a <| eta_a) ; mu_a ~ id_a`. -/
  | rightUnit : BunchedBimonoidUnitCounitRow bunchedBimonoidUnitIntoMuCell
      bunchedBimonoidIdentityStrandCell
  /-- Left unit `(eta_a |> a) ; mu_a ~ id_a`. -/
  | leftUnit : BunchedBimonoidUnitCounitRow bunchedBimonoidLeftUnitLawLeftLeg
      bunchedBimonoidIdentityStrandCell
  /-- Right counit `delta_a ; (a <| eps_a) ~ id_a`. -/
  | rightCounit : BunchedBimonoidUnitCounitRow bunchedBimonoidDeltaIntoCounitCell
      bunchedBimonoidIdentityStrandCell
  /-- Left counit `delta_a ; (eps_a |> a) ~ id_a`. -/
  | leftCounit : BunchedBimonoidUnitCounitRow bunchedBimonoidLeftCounitLawLeftLeg
      bunchedBimonoidIdentityStrandCell

/-- ★ **Every (co)unit row is matrix-sound** — both legs of each row evaluate to `[[1]]` under the shipped
plain `Mat(N)` functor (`rfl` per row; full-enumeration match, no wildcard). -/
theorem bunchedBimonoidUnitCounitRowMatrixSound {d : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad d}
    (row : BunchedBimonoidUnitCounitRow cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta := by
  match row with
  | .rightUnit => rfl
  | .leftUnit => rfl
  | .rightCounit => rfl
  | .leftCounit => rfl

/-! # =========================================================================================
    # THE UNITAL SCOPE + THE RE-STATED TARGET
    # =========================================================================================
-/

/-- ★★ **The unital star scope** — the r4 star scope widened by the four (co)unit rows: the honest Lafont /
Pirashvili / Fox presentation of the additive bicommutative-bimonoid PROP, at last with its units. -/
def bunchedBimonoidUnitalStarCongruenceScope : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
    (fun {d} cellAlpha cellBeta => @BunchedBimonoidUnitCounitRow d cellAlpha cellBeta)

/-- Star-scope convertibility embeds into the unital scope (monotonicity of the saturated congruence). -/
theorem bunchedBimonoidStarConvEmbedsIntoUnital {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      cellAlpha cellBeta := by
  induction conv with
  | ofRelation row => exact SaturatedConvOverWithId.ofRelation (Or.inl row)
  | vcompCongrLeft cellBetaFixed _ ih => exact SaturatedConvOverWithId.vcompCongrLeft cellBetaFixed ih
  | vcompCongrRight cellAlphaFixed _ ih =>
      exact SaturatedConvOverWithId.vcompCongrRight cellAlphaFixed ih
  | whiskerLeftCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell ih
  | whiskerRightCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightCongr whiskeringCell ih
  | idCongr _ ih => exact SaturatedConvOverWithId.idCongr ih
  | whiskerLeftWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftWhiskerCongr innerCell ih
  | whiskerRightWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightWhiskerCongr innerCell ih
  | refl cell => exact SaturatedConvOverWithId.refl cell
  | symm _ ih => exact SaturatedConvOverWithId.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOverWithId.trans ihLeft ihRight

/-- ★★★ **THE UNITAL COMPLETENESS TARGET, NAMED (NOT proven).**  Dimension pinned to 2; additivity,
well-typedness, canonical generator nodes; equal plain `Mat(N)` matrices imply convertibility over the UNITAL
scope.  Every decided refutation datum is excluded by a machine-checked lever: the r6/r7/r29 leaks by the
premises, and the r30 unit pair by the widened scope itself (`bunchedBimonoidUnitPairConvertsUnital`). -/
def bunchedBimonoidStarStatementDimTwoCanonicalGensUnital : Prop :=
  ∀ (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad 2),
    bunchedBimonoidCellUsesOnlyAdditive cellAlpha = true →
    bunchedBimonoidCellUsesOnlyAdditive cellBeta = true →
    bunchedBimonoidCellWellTyped cellAlpha →
    bunchedBimonoidCellWellTyped cellBeta →
    bunchedBimonoidCellGensCanonical cellAlpha →
    bunchedBimonoidCellGensCanonical cellBeta →
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      cellAlpha cellBeta

/-! # =========================================================================================
    # THE HONESTY FIRES
    # =========================================================================================
-/

/-- ★★ **The r30 refutation pair CONVERTS over the unital scope** — the correction closes exactly the
decided hole (a one-row fire). -/
theorem bunchedBimonoidUnitPairConvertsUnital :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      bunchedBimonoidUnitIntoMuCell bunchedBimonoidIdentityStrandCell :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidUnitCounitRow.rightUnit)

/-- The counit-side pair converts too. -/
theorem bunchedBimonoidCounitPairConvertsUnital :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      bunchedBimonoidDeltaIntoCounitCell bunchedBimonoidIdentityStrandCell :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidUnitCounitRow.rightCounit)

/-- ★★ **The r30 affine-offset invariant is DEAD against the unital scope** — the right-unit row relates
cells with DIFFERENT augmented values, so the gated affine absorber cannot extend to the widened scope: the
unital siege is genuinely open, not re-refutable by the r30 separator. -/
theorem bunchedBimonoidUnitRowBreaksAffineInvariant :
    bunchedBimonoidEvalAugCell bunchedBimonoidUnitIntoMuCell
      ≠ bunchedBimonoidEvalAugCell bunchedBimonoidIdentityStrandCell :=
  bunchedBimonoidUnitIntoMuAugValueSeparates

/-! # =========================================================================================
    # THE MARKERS — the unital siege opens honestly
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — the unital re-statement.**  `= true` records the four matrix-sound (co)unit rows,
the widened scope with the monotone embedding of every shipped star-scope convertibility, the re-stated
target `bunchedBimonoidStarStatementDimTwoCanonicalGensUnital`, the closure fire on the exact r30 refutation
pair, and the death of the r30 separator against the widened scope. -/
def fxBunchedBimonoid_starUnitalRestatementShipped : Bool := true

/-- ★ **THE UNITAL STAR IS NAMED, NOT PROVEN — the new owner (no flip).**  `= false` records that
`bunchedBimonoidStarStatementDimTwoCanonicalGensUnital` is NOT proven.  The bill is the r29 successor brief
re-aimed at the unital scope: (i) the total retract to the spider normal form (the `vcomp` case consumes the
r29-delivered block-threading; the general `wideSwap(m,n)` riffle recursion remains the r8 gate); (ii) the
r26 recComb perm middle; (iii) the assembly — PLUS the fresh unital obligations the r30 decision surfaced
(eta-absorption into folds and eps-absorption into fans along the retract).  This marker flips ONLY with the
unital star genuinely proven. -/
def fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen : Bool := false

end FX1Poly.Polygraph.Omega
