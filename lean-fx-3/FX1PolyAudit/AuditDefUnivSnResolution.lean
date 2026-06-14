import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.DefUnivSnResolution

/-! # AuditDefUnivSnResolution — zero-axiom gate for the DEFUNIV-SN (#1412) verdict

The univalence-shaped demo rule is already RPO-orientable (its reduct
shrinks), so it inherits the shipped Tier-2 oriented-SN with no bespoke
`lex(level, size)` measure.  Each pin must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_isStructurallyRecursive
#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_avoidsSubstitution
#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_isRpoOrientable

end FX1PolyAudit
