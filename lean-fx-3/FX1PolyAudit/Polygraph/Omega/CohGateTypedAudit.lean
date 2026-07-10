import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CohGateTyped

/-! # FX1PolyAudit.Polygraph.Omega.CohGateTypedAudit — zero-axiom gate for the typed coh fullness gate
(OMEGA-6 r2, B2).

Per-declaration `#assert_no_axioms` on the support / level machinery (`varsOfTeleType` / `levelsUpTo` /
`natElem`), the CaTT fullness decision (`cohFullnessCheck`), the typed coh row's forgetful map
(`cohRowTypedForget`), the positive witness (`arrowDiskPsContext` + its typed check, `arrowDiskCohRow`,
`arrowDiskCohRowTyped` + fullness-holds + forget-identity), and the LOAD-BEARING rejection witness
(`interchangeMissingMiddleCoh` + r1-admits + `_fullnessFails`). -/

namespace FX1PolyAudit

-- CohGateTyped.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.varsOfTeleType
#assert_no_axioms FX1Poly.Polygraph.Omega.levelsUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.natElem
#assert_no_axioms FX1Poly.Polygraph.Omega.cohFullnessCheck
#assert_no_axioms FX1Poly.Polygraph.Omega.cohRowTypedForget
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskPsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskPsContext_psTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskCohRow
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskCohRowTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskCohRowTyped_fullnessHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.arrowDiskCohRowTyped_forgetIsUnderlying
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeMissingMiddleCoh
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeMissingMiddleCoh_r1Admits
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeMissingMiddleCoh_fullnessFails

end FX1PolyAudit
