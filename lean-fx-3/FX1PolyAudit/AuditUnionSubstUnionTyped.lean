import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped

/-! # FX1PolyAudit/AuditUnionSubstUnionTyped — native substitution-condition zero-axiom gate

Per-declaration zero-axiom gate for `FX1Poly/Typed/Engine/Union/HasTypeUnionSubstUnionTyped.lean`: the
native substitution-context condition `HasTypeUnion.SubstUnionTyped` and its one/two-binder lift API
(`cons` / `consTwice`).  The `cons` zero-case types the fresh `var 0` through the native `HasTypeUnion.var`
(no `ofGrown`), and the shifted images through the native `HasTypeUnion.weakenUnderBinding`.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.cons
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.consTwice

end FX1PolyAudit
