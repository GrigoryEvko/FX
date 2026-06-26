import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.RawTermSize

/-! # FX1PolyAudit.Tier0.Term.RawTermSize — zero-axiom gate (the structural size measure)

Per-declaration zero-axiom gate for the `RawTerm` / `RawTermChildren` structural size + the child strict-decrease
lemmas (the well-foundedness foundation for fuel-bounded recursion). The mutual structural recursion is the
propext-risk point — this gate certifies it clean. Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.size
#assert_no_axioms FX1Poly.Core.RawTermChildren.size
#assert_no_axioms FX1Poly.Core.RawTerm.size_mkGen
#assert_no_axioms FX1Poly.Core.RawTermChildren.size_childNil
#assert_no_axioms FX1Poly.Core.RawTermChildren.size_childCons
#assert_no_axioms FX1Poly.Core.RawTermChildren.size_lt_mkGen
#assert_no_axioms FX1Poly.Core.RawTermChildren.childHead_size_lt
#assert_no_axioms FX1Poly.Core.RawTermChildren.childTail_size_lt
#assert_no_axioms FX1Poly.Core.RawTerm.childHead_size_lt_ofConsSpine

end FX1PolyAudit
