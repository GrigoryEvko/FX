import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportRowConfluence

/-! # FX1PolyAudit/AuditSizeGrowingTransportRowConfluence — zero-axiom gate for the demo-row Newman route

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportRowConfluence.lean`:
the congruence-closure lifts, the `Joinable` transports, the single-step congruence lifts, the crucial
`fire`-vs-`cong` join (`demoFireCongJoin`), the mutual local-confluence proof (`demoStep_localConfluent`),
weak confluence, and Church-Rosser via the GENERIC Newman (`sizeGrowingTransportDemo_confluent`).

This is the demonstration that the Newman route (SN + local confluence ⇒ confluence) works for a row whose
rule CREATES redexes — exactly where the univalence row's one-pass `univNF` shortcut cannot apply.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`
— the indexed-`cases` critical-pair analysis stays axiom-clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.joinableSymm
#assert_no_axioms FX1Poly.Core.demoReflTransClosure_cong
#assert_no_axioms FX1Poly.Core.demoReflTransClosure_here
#assert_no_axioms FX1Poly.Core.demoReflTransClosure_there
#assert_no_axioms FX1Poly.Core.joinableChildrenToTerm
#assert_no_axioms FX1Poly.Core.joinableHeadToChildren
#assert_no_axioms FX1Poly.Core.joinableTailToChildren
#assert_no_axioms FX1Poly.Core.demoStep_liftGlueElim
#assert_no_axioms FX1Poly.Core.demoStep_liftPairHead
#assert_no_axioms FX1Poly.Core.demoStep_liftPairTail
#assert_no_axioms FX1Poly.Core.demoFireCongJoin
#assert_no_axioms FX1Poly.Core.demoStep_localConfluent
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemo_weaklyConfluent
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemo_confluent

end FX1PolyAudit
