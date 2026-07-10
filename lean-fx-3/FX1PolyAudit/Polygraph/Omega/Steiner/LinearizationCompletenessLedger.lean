import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.LinearizationCompletenessLedger

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/LinearizationCompletenessLedger — zero-axiom gate (OMEGA-2.5 r1, B5)

Per-declaration `#assert_no_axioms` on the completeness scope + ledger: the atom-word boundary
degeneracy, the pole-determination regression, the chain-table crown iff on `IsAtomWord`, and the honesty
markers.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The completeness-scope regression theorems
#assert_no_axioms FX1Poly.Polygraph.Omega.boundarySource_atomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.polesOf_atomWord_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.atomWord_conv_iff_linearizeFull_eq

-- The honesty markers (the ledger)
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_chainCarrierShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_whiskerFixAcceptanceTest
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_chainSoundnessUniversal
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_completenessRegressesOnAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_generalCompletenessOpenIdCongr
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega25_r1Complete

end FX1PolyAudit
