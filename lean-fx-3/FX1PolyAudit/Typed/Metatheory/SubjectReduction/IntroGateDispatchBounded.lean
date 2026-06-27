import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateDispatchBounded

/-! # FX1PolyAudit/.../IntroGateDispatchBounded — zero-axiom gate for the bounded intro-congruence gate

Per-declaration zero-axiom gate for the fuel-bounded introducer-congruence gate inhabitant
(`HasTypeUnion.unionIntroCongruenceClosesBoundedGate`, the intro third of the SR-WF-TIEOFF bounded congruence
master, modulo the one A1-blocked `pathLam` premise).  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionIntroCongruenceClosesBoundedGate

end FX1PolyAudit
