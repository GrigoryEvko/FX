import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderConsistency

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderConsistency — zero-axiom gate for the r16
upgraded-reader assembly, decision-consistency regression, and JAM A re-audit (WP-AMALG-2 r16, B4)

Per-declaration zero-axiom gate for the shallow-vs-upgraded slot counts, the r15 three-pairs decision consistency,
the reseat-refusal consistency, the JAM A narrowing, and the two honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.shallowReaderWhiskerSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.upgradedReaderWhiskerSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR16DecisionConsistency
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR16RefusalConsistency
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconR16JamANarrowed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_upgradedReaderNoVerdictChange
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_jamANarrowedByCanonicalReader

end FX1PolyAudit
