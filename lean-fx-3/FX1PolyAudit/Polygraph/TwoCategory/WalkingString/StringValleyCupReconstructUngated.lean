import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstructUngated

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupReconstructUngated — zero-axiom gate
(FC-3 r34, Piece-II cup assembly closed: the UNCONDITIONAL cup-side `DiagramType.ext`, over the walking
ADJOINT-TRIPLE signature)

Per-declaration zero-axiom gate for the un-gated cup-side reconstruction: the UNCONDITIONAL
`stringCupRestrict_reconstructs_unconditional` (case-3 gate discharged by the ported `stringCupTopTopPartner`) and
its wide-valley firing `stringCupRestrict_reconstructs_unconditional_firesOnWideValley`.  Every declaration must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs_unconditional
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs_unconditional_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupRestrictReconstructsUnconditional

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs_unconditional
#print axioms FX1Poly.Polygraph.stringCupRestrict_reconstructs_unconditional_firesOnWideValley
#print axioms FX1Poly.Polygraph.fxString_hasCupRestrictReconstructsUnconditional

end FX1PolyAudit
