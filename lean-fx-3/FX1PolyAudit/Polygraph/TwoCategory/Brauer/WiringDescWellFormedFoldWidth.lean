import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldWidth

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldWidth — zero-axiom gate (BRAUER r21)

Per-declaration zero-axiom gate for the corrected-word GENERAL `WellFormedBrauerFold` assembly: A′
(`throughStrandPerm_isBounded`), the cap SHRINK / cup GROW block width laws (`capBlockOpenWiresShrinkWidth` /
`cupBlockOpenWiresGrowWidth`), the seed width (`brauerSeedOpenWiresLengthWidth`), the concrete-output truth-probe,
the general theorem (`wellFormedBrauerFold_correctedWord_general`) and its non-vacuity exercises, and the r21 marker.
The general theorem transitively covers every re-derived private helper (the `propext`-free `Nat` / `Bool` / list
kit, the `arcMiddleCountBelow` rank lemmas, the single-step cap/cup length lemmas, and the range helpers).

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any axioms".
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- A′: the through permutation is `[0, #through)`-bounded
#assert_no_axioms FX1Poly.Polygraph.throughStrandPerm_isBounded

-- the cap SHRINK / cup GROW block width laws + the seed width + the concrete-output truth-probe
#assert_no_axioms FX1Poly.Polygraph.capBlockOpenWiresShrinkWidth
#assert_no_axioms FX1Poly.Polygraph.cupBlockOpenWiresGrowWidth
#assert_no_axioms FX1Poly.Polygraph.brauerSeedOpenWiresLengthWidth
#assert_no_axioms FX1Poly.Polygraph.widthBridges_probe

-- ★ the GENERAL corrected-word WellFormedBrauerFold + its non-vacuity exercises + the r21 marker
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_general
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_allCapsBoundary
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_general_allCapsBoundary
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_general_wildThrough
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_correctedWord_general_wildCupLoop
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedWordGeneralWellFormed

end FX1PolyAudit
