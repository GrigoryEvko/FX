import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.ConvertibilitySoundness

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.ConvertibilitySoundness — zero-axiom gate
(LAFONT-PROP r2, brick B: RESIDUAL 1 DISCHARGED)

Per-declaration zero-axiom gate for the congruence-closure soundness lift: the own
distributivity/associativity kit, the index-decomposition and cancellation lemmas, the
structural-sum split/exchange (Fubini) kit, THE CONGRUENCE SOUNDNESS THEOREM
(`convertibleDiagramsDenoteEqualMatrices`, discharging the r1 named residual as
`convertibilityMatrixSoundnessHolds`), the non-convertibility contrapositive
(`notConvertibleOfDistinctMatrices`), and the consumption fire.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.noLtOfGe
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bleFalseGivesReverseLt
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leOfBltIsFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leGivesAddSubCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decomposeIndexAgainstBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leOfAddLeAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.ltOfAddLtAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.beqAddLeftCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mulAddDistribLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addFourExchange
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addMulDistribRight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mulAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowRespectsPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowSplitsAtBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowOfPointwiseAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowMulLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowMulRight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowExchange
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.convertibleDiagramsDenoteEqualMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.convertibilityMatrixSoundnessHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.notConvertibleOfDistinctMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.derivedChainMatricesAgreeViaSoundness

end FX1PolyAudit
