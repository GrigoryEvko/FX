import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.AgreementBattery

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/AgreementBattery — zero-axiom gate (OMEGA-2 r2, B2)

Per-declaration `#assert_no_axioms` on the eval-level two-decider falsifier: the two `Bool` deciders
(`freeDecide` = FREE-7 `decideTwoCellConvFull`, `steinerDecide` = `decideFreeConvSound o toCellDimTwo`),
the battery cells, the eight agreement rows (each `freeDecide = steinerDecide` by `rfl`), the per-row
verdict values, and the battery-passes marker.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — so the agreement being asserted
by `rfl`/`decide` is genuinely axiom-clean (the falsifier is a real check, not a smuggled assumption). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.freeDecide
#assert_no_axioms FX1Poly.Polygraph.Omega.steinerDecide
#assert_no_axioms FX1Poly.Polygraph.Omega.cellAlpha
#assert_no_axioms FX1Poly.Polygraph.Omega.cellBeta
#assert_no_axioms FX1Poly.Polygraph.Omega.cellIdEdgeF
#assert_no_axioms FX1Poly.Polygraph.Omega.cellIdEdgeG
#assert_no_axioms FX1Poly.Polygraph.Omega.cellUnitLeftAlpha
#assert_no_axioms FX1Poly.Polygraph.Omega.cellUnitRightAlpha
#assert_no_axioms FX1Poly.Polygraph.Omega.cellAssocLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.cellAssocRight
#assert_no_axioms FX1Poly.Polygraph.Omega.cellUnitLeftBeta
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementUnitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementUnitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementUnitBeta
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementReflexive
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementDistinctGenerators
#assert_no_axioms FX1Poly.Polygraph.Omega.agreementStructuralNonRelated
#assert_no_axioms FX1Poly.Polygraph.Omega.verdicts_true
#assert_no_axioms FX1Poly.Polygraph.Omega.verdicts_false
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_agreementBatteryPasses

end FX1PolyAudit
