import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseAbsorptionFires

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseAbsorptionFires — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 2, fire file)

Per-declaration zero-axiom gate for the absorption fires: the fire matrix, the three
concrete absorptions (eta / epsilon / wire) with their soundness consumption and kernel-`rfl`
matrix pins, the fan-annihilation and zero-fan fires, and the distinct-matrix negative
control.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFireMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaAbsorptionFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaAbsorptionFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaAbsorptionMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEpsilonAbsorptionFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEpsilonAbsorptionMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireAbsorptionFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireAbsorptionMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFreshZeroFanFireDenotesIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstZeroFanFireDenotesPaddedDiscard
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDistinctCanonicalFormsStayApart

end FX1PolyAudit
