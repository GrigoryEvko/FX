import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.AxisObligation

/-! # FX1PolyAudit.Axis.Context.AxisObligation — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.CapabilityStatus.isBelow_refl
#assert_no_axioms FX1Poly.Axis.CapabilityStatus.meet_isBelow_left
#assert_no_axioms FX1Poly.Axis.CapabilityStatus.meet_isBelow_right
#assert_no_axioms FX1Poly.Axis.CapabilityStatus.isBelow_trans
#assert_no_axioms FX1Poly.Axis.CapabilityStatus.isBelow_antisymm
#assert_no_axioms FX1Poly.Axis.CapabilityStatus.isBelow_meet_iff
#assert_no_axioms FX1Poly.Axis.MetatheoreticCapabilities.isBelow_refl
#assert_no_axioms FX1Poly.Axis.MetatheoreticCapabilities.meet_isBelow_left
#assert_no_axioms FX1Poly.Axis.MetatheoreticCapabilities.meet_isBelow_right
#assert_no_axioms FX1Poly.Axis.MetatheoreticCapabilities.isBelow_trans

end FX1PolyAudit
