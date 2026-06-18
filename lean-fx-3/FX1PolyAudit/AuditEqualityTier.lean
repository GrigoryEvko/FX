import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.EqualityTier

/-! # FX1PolyAudit/AuditEqualityTier — zero-axiom gate for the definitionality ledger

Per-declaration zero-axiom gate for `FX1Poly/Typed/Engine/Classifier/EqualityTier.lean`: the door/tier
taxonomy (`EqualityDoor` / `EqualityTier`), the iota/eta/erase classifiers, the per-row spot-checks, the
definitionality counts over the shipped tables, the non-vacuity discriminators, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the classifier records what the shipped certificates prove and adds no new
metatheory. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.iotaRowDoor
#assert_no_axioms FX1Poly.Typed.iotaRowTier
#assert_no_axioms FX1Poly.Typed.etaRowDoor
#assert_no_axioms FX1Poly.Typed.etaRowTier
#assert_no_axioms FX1Poly.Typed.etaRowIsTypedDirected
#assert_no_axioms FX1Poly.Typed.etaRowIsRawDefinitional
#assert_no_axioms FX1Poly.Typed.gradeZeroEraseDoor
#assert_no_axioms FX1Poly.Typed.gradeZeroEraseTier
#assert_no_axioms FX1Poly.Typed.gelBetaIotaRow_door
#assert_no_axioms FX1Poly.Typed.gelBetaIotaRow_tier
#assert_no_axioms FX1Poly.Typed.gelEtaRow_door
#assert_no_axioms FX1Poly.Typed.gelEtaRow_tier
#assert_no_axioms FX1Poly.Typed.iotaRowCount
#assert_no_axioms FX1Poly.Typed.noShippedIotaRowIsPropositional
#assert_no_axioms FX1Poly.Typed.etaTypedDirectedCount
#assert_no_axioms FX1Poly.Typed.etaRawDefinitionalCount
#assert_no_axioms FX1Poly.Typed.noShippedEtaRowIsPropositional
#assert_no_axioms FX1Poly.Typed.equalityTier_discriminates
#assert_no_axioms FX1Poly.Typed.equalityDoor_discriminates
#assert_no_axioms FX1Poly.Typed.fxEqualityTier_claimsGlobalDefinitionalConv
#assert_no_axioms FX1Poly.Typed.fxEqualityTier_hasSPropEraseInstance

end FX1PolyAudit
