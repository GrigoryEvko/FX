import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Strengthening.PlateauDescentSubstrate

/-! # FX1PolyAudit.Typed.Metatheory.Strengthening.PlateauDescentSubstrate — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_lamCell_body
#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_appCell_function
#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_appCell_argument
#assert_no_axioms FX1Poly.Typed.appNormal_argumentNormal
#assert_no_axioms FX1Poly.Typed.lamNormal_bodyNormal
#assert_no_axioms FX1Poly.Typed.RawTerm.isStepNormalForm_childrenNormal
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_head
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_tail

end FX1PolyAudit
