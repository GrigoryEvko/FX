import FX1Poly.Polygraph.Omega.Suspension
import FX1Poly.Polygraph.Omega.CongruenceWithId

/-! # Polygraph/Omega/SuspensionWithId — suspension preserves the idCongr sibling (OMEGA-3 r2, B2)

★ **Preservation over the sibling is FREE.**  The shipped `suspendPreservesStrictConv` (`Suspension.lean`)
embeds the 8-constructor free strict congruence one dimension up.  Over the idCongr-extended sibling the
same embedding holds with THREE additional arms, each a `suspendCell` homomorphism step (`rfl`):
`suspendCell (id a) = id (suspendCell a)`, `suspendCell (whiskerLeft w c) = whiskerLeft (suspendCell w)
(suspendCell c)`, and the right-whisker dual — so `idCongr` and the two whisker-1-cell congruences lift by
their namesake sibling constructors on the inductive hypothesis. -/

namespace FX1Poly.Polygraph.Omega

/-- ★ **PRESERVATION over the sibling.**  If `a` and `b` are idCongr-convertible, their suspensions are
convertible one dimension up.  The 11-arm induction maps `ofRelation` through `suspendStrictRow`, the eight
shipped shapes through the `suspendCell` homomorphism, and the three new shapes (`idCongr`, the two
whisker-1-cell congruences) through their namesake sibling constructors — each a `rfl` homomorphism step. -/
theorem suspendPreservesStrictConvWithId {computad : OmegaComputad} {dim : Nat}
    {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    SaturatedConvOverWithId (suspendComputad computad) (StrictAxiomRel (suspendComputad computad))
      (suspendCell cellAlpha) (suspendCell cellBeta) := by
  induction conv with
  | ofRelation row => exact SaturatedConvOverWithId.ofRelation (suspendStrictRow row)
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOverWithId.vcompCongrLeft (suspendCell cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOverWithId.vcompCongrRight (suspendCell cellAlpha) ih
  | whiskerLeftCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftCongr (suspendCell whiskeringCell) ih
  | whiskerRightCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightCongr (suspendCell whiskeringCell) ih
  | idCongr _ ih => exact SaturatedConvOverWithId.idCongr ih
  | whiskerLeftWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftWhiskerCongr (suspendCell innerCell) ih
  | whiskerRightWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightWhiskerCongr (suspendCell innerCell) ih
  | refl cell => exact SaturatedConvOverWithId.refl (suspendCell cell)
  | symm _ ih => exact SaturatedConvOverWithId.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOverWithId.trans ihLeft ihRight

end FX1Poly.Polygraph.Omega
