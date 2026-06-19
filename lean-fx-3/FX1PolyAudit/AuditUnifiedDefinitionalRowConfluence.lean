import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnifiedDefinitionalRowConfluence

/-! # FX1PolyAudit/AuditUnifiedDefinitionalRowConfluence — zero-axiom gate for the joint-row Newman route

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/UnifiedDefinitionalRowConfluence.lean`:
the univalence-side single-step congruence lifts, the demo-side lifts into an `equivCode` child, the
cross-relation commuting diamond (`univStepDemoStepCommute`), the union `Joinable` lifts, the four-way local
confluence (`unifiedDefinitionalRow_weaklyConfluent`), and Church-Rosser of the joint row via the GENERIC
Newman (`unifiedDefinitionalRow_confluent`).

This is the modular-confluence capstone for definitional univalence: the no-new-redexes univalence row
(confluent the easy way via `univNF`) and the redex-creating size-growing demo row (confluent via genuine
Newman) glue into a confluent union, with the only cross-interaction — `gen_idCode` vs `gen_glueElim`,
disjoint heads, zero critical pairs — resolved by the commuting diamond.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — the indexed-`cases`
cross-relation analysis stays axiom-clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.univStep_liftGlueElim
#assert_no_axioms FX1Poly.Core.univStep_liftPairHead
#assert_no_axioms FX1Poly.Core.univStep_liftPairTail
#assert_no_axioms FX1Poly.Core.demoStep_liftEquivHead
#assert_no_axioms FX1Poly.Core.demoStep_liftEquivTail
#assert_no_axioms FX1Poly.Core.univStepDemoStepCommute
#assert_no_axioms FX1Poly.Core.joinableUnivToUnion
#assert_no_axioms FX1Poly.Core.joinableDemoToUnion
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_weaklyConfluent
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_confluent
#assert_no_axioms FX1Poly.Core.fxUnifiedDefinitionalRowConfluent_viaGenuineNewman
#assert_no_axioms FX1Poly.Core.fxUnifiedDefinitionalRowConfluent_shipsDecidableConv

end FX1PolyAudit
