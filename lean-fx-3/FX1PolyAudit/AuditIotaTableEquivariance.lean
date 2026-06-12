import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableEquivarianceSubstrate

/-! # FX1PolyAudit/AuditIotaTableEquivariance — IOTA-T2 audit shard (equivariance substrate)

Per-declaration zero-axiom gate for the IOTA-T2 substrate: the fold-engine lift-iterate pins, the
shift-erased view under substitution (substView / lookup-map / per-shift projections), the
depth-weakening naturality (term, one-binder body, two-binder body — with the under-binder naturality
squares), and slot-replacement naturality.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Lift-iterate pins -/

#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_zero
#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_succ

/-! ## The shift-erased view under substitution -/

#assert_no_axioms FX1Poly.Core.ScopedChild.substView
#assert_no_axioms FX1Poly.Core.listEntryAt?_map
#assert_no_axioms FX1Poly.Core.RawTermChildren.toScopedChildren_subst
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftZero?_substView
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftOne?_substView
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftTwo?_substView

/-! ## Depth-weakening naturality -/

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy_subst
#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLift_renameLiftWeaken
#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLiftLift_renameLiftLiftWeaken
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderOneBinderBy_subst
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderTwoBindersBy_subst

/-! ## Slot replacement naturality -/

#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?_subst

end FX1PolyAudit
