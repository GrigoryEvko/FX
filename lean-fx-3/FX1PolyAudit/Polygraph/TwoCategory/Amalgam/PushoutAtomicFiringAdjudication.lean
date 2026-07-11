import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAtomicFiringAdjudication

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutAtomicFiringAdjudication — zero-axiom gate
(WP-AMALG-2 r14, Brick B3: the atomic-firing adjudication — the finest payload zip is BYPASSED)

Per-declaration zero-axiom gate for the adjudication: the r8-faces refusal witness, the machine-checked
marker conjunction, and the bypass marker. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAdjudicationRefusesR8Faces
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAtomicFiringAdjudication
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconAtomicFiringAdjudication_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_atomicFiringZipBypassed

end FX1PolyAudit
