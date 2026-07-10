import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWireChangeLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWireChangeLedger — zero-axiom gate for the r6 ledger
(WP-AMALG-2 r6, B3/B5)

Per-declaration zero-axiom gate for the four r6 honesty markers (the reseat-object demotion, the
factorization-completeness wall, the #2140 H2-EXT handoff, the no-flip narrowing verdict).  These are `Bool`
markers; the gate confirms they are axiom-free.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_wordMulReseatObjectExists
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_factorizationCompletenessStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_h2ExtCocycleHandoff
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r6NarrowsWireChangeResidual

end FX1PolyAudit
