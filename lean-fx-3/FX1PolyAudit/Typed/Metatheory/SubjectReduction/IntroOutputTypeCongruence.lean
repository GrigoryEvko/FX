import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroOutputTypeCongruence

/-! # FX1PolyAudit/AuditIntroOutputTypeCongruence — introducer output-type congruence audit shard

Per-declaration zero-axiom gate for the `intro`-arm output-type Conv-stability of the general union SR (the
introducer half of the eliminator-congruence ingredient, #1740 / #1697): the two non-trivial introducer rows
`lam` (`...UnderDomainStep`, via `Conv.ofChildren` piTyCode congruence) and `pathLam`
(`...UnderBodyStep`, via `Conv.subst0` body-leg congruence on both bridge endpoints).  Each must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.lamIntroOutputType_isConvStableUnderDomainStep
#assert_no_axioms FX1Poly.Typed.pathLamIntroOutputType_isConvStableUnderBodyStep

end FX1PolyAudit
