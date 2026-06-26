import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded — zero-axiom gate

Per-declaration zero-axiom gate for the fuel-bounded single-step-SR predicate frame (SR-WF-TIEOFF step 1): the
bounded predicate, the universal→bounded forgetful map, the antitone weakening, and the closure enabler. Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionBelow
#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReduction.toBelow
#assert_no_axioms FX1Poly.Typed.UnionChildSubjectReductionBelow.weaken
#assert_no_axioms FX1Poly.Typed.unionChildSubjectReductionOfAllBelow

end FX1PolyAudit
