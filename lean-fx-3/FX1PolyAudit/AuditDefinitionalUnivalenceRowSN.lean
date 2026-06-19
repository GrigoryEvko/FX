import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.DefinitionalUnivalenceRowSN

/-! # FX1PolyAudit/AuditDefinitionalUnivalenceRowSN — zero-axiom gate for the univalence-row SN

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/DefinitionalUnivalenceRowSN.lean`:
the univalence-row congruence closure's size-decrease (`UnivalenceRowStep.sizeStrictlyDecreases`), the
headline well-foundedness (`univalenceRowStep_wellFounded`) and accessibility
(`UnivalenceRowStep.isStronglyNormalizing`), the shipped-rule firing link
(`univalenceRowStep_fireMatchesShippedRow`), the congruence-arm non-vacuity (`univalenceRowStep_congSmoke`),
and the honest markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the first instantiated WellFounded for a table-native oriented row, by the
structural `RawTerm.size` measure, with no RPO/Tait/beta-SN import. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.UnivalenceRowStep.sizeStrictlyDecreases
#assert_no_axioms FX1Poly.Core.univalenceRowStep_wellFounded
#assert_no_axioms FX1Poly.Core.UnivalenceRowStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.univalenceRowStep_fireMatchesShippedRow
#assert_no_axioms FX1Poly.Core.univalenceRowStep_congSmoke
#assert_no_axioms FX1Poly.Core.UnivalenceRowStep.toStepOverTable
#assert_no_axioms FX1Poly.Core.fxUnivalenceRowSN_isSizeMeasureNotRpo
#assert_no_axioms FX1Poly.Core.fxUnivalenceRowSN_isJointWithBetaIota
#assert_no_axioms FX1Poly.Core.fxUnivalenceRowSN_coversShippedTableRelationVerbatim

end FX1PolyAudit
