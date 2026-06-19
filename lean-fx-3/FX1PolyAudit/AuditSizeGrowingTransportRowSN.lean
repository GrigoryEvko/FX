import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportRowSN

/-! # FX1PolyAudit/AuditSizeGrowingTransportRowSN — zero-axiom gate for the size-GROWING row SN

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportRowSN.lean`:
the type-complexity measure (`RawTerm.productFormerCount` + its spot-checks), the size-growing demo
closure's strict measure-decrease (`SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases`), the
headline well-foundedness (`sizeGrowingTransportDemo_wellFounded`) and accessibility, the genuine
size-growth witness (`sizeGrowingTransportDemo_rootGrowsSize` — a `decide`, must stay axiom-free), the
congruence-arm non-vacuity, and the honest markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the first instantiated WellFounded for a SIZE-GROWING oriented row, by a
type-complexity measure that decreases on every step (no RPO, no Tait). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.productFormerCount
#assert_no_axioms FX1Poly.Core.productFormerCount_glueElim
#assert_no_axioms FX1Poly.Core.productFormerCount_pair
#assert_no_axioms FX1Poly.Core.productFormerCount_productCode
#assert_no_axioms FX1Poly.Core.SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemo_wellFounded
#assert_no_axioms FX1Poly.Core.SizeGrowingTransportDemoStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemo_rootGrowsSize
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemo_congSmoke
#assert_no_axioms FX1Poly.Core.fxSizeGrowingDemo_isGenuinelySizeGrowing
#assert_no_axioms FX1Poly.Core.fxSizeGrowingDemo_measureDecreasesEveryStep
#assert_no_axioms FX1Poly.Core.fxSizeGrowingDemo_isNonDuplicating
#assert_no_axioms FX1Poly.Core.fxShippedSizeGrowingRows_needTait

end FX1PolyAudit
