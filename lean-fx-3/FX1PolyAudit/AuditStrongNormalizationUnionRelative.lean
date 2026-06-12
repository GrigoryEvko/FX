import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StrongNormalizationUnionRelative

/-! # FX1PolyAudit/AuditStrongNormalizationUnionRelative — ETA-T6
inc-4 shard

Per-declaration zero-axiom gate for the class-relativized Geser
engine: the relativized quasi-commutation, its trivial global
embedding, the inner induction with the membership threaded, and the
★ relativized criterion `accUnionOn`.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.QuasiCommutesRightOverLeftOn
#assert_no_axioms FX1Poly.Core.QuasiCommutesRightOverLeftOn.ofGlobal
#assert_no_axioms FX1Poly.Core.accUnionInnerOn
#assert_no_axioms FX1Poly.Core.accUnionOn

end FX1PolyAudit
