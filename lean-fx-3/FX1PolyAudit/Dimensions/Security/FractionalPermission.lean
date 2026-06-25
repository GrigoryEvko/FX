import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Security.FractionalPermission

/-! # FX1PolyAudit.Dimensions.Security.FractionalPermission — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.Permission.fitsWhole
#assert_no_axioms FX1Poly.Modal.Permission.add
#assert_no_axioms FX1Poly.Modal.Permission.naiveAdd
#assert_no_axioms FX1Poly.Modal.Permission.zero_add
#assert_no_axioms FX1Poly.Modal.Permission.add_zero
#assert_no_axioms FX1Poly.Modal.Permission.conflict_add
#assert_no_axioms FX1Poly.Modal.Permission.add_conflict
#assert_no_axioms FX1Poly.Modal.Permission.add_comm
#assert_no_axioms FX1Poly.Modal.Permission.add_neverOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveAddOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveOverallocationDoesNotFit
#assert_no_axioms FX1Poly.Modal.Permission.soundAddRejectsOverallocation
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullFits
#assert_no_axioms FX1Poly.Modal.Permission.fracPartialAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.hasPositiveDenom
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc_smoke

end FX1PolyAudit
