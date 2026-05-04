import LeanFX2.HoTT.FunextFull

/-! # Smoke/AuditFunextFull — Audit gates for HoTT/FunextFull.

Verifies every shipped declaration in `HoTT/FunextFull.lean` audits
zero-axiom under `#print axioms`.

## Scope

* **§1 pointwise function equality predicate** (3 decls):
  - `pointwiseRefl`
  - `pointwiseSymm`
  - `pointwiseTrans`

* **§2 funext-β forward direction round-trip** (3 decls):
  - `fnEqToPointwise_pointwise_atSelf`
  - `fnEqToPointwise_trans_refl_refl`
  - `fnEqToPointwise_symm_refl`

* **§3 backward map round-trip** (2 decls):
  - `pointwiseMetaToFnEqAtRefl_forgetful`
  - `pointwiseMetaToFnEqAtRefl_trivial`

* **§4 kernel-meta correspondence** (1 decl):
  - `kernelMetaCorrespondence_atRefl`

* **§5 round-trip identity (rfl-fragment)** (3 decls):
  - `roundTripPathSide_refl`
  - `roundTripPointwiseSide_trivial`
  - `roundTripPointwiseSide_anyPointwise`

* **§6 application laws** (3 decls):
  - `applicationAtRefl`
  - `eqSubst_functionEquality`
  - `transport_at_pointwise_refl`

Total: 15 zero-axiom shipped declarations.
-/

namespace LeanFX2

/-! ## §1. Pointwise function equality predicate. -/

#print axioms LeanFX2.Funext.pointwiseRefl
#print axioms LeanFX2.Funext.pointwiseSymm
#print axioms LeanFX2.Funext.pointwiseTrans

/-! ## §2. Funext-β forward direction round-trip. -/

#print axioms LeanFX2.Funext.fnEqToPointwise_pointwise_atSelf
#print axioms LeanFX2.Funext.fnEqToPointwise_trans_refl_refl
#print axioms LeanFX2.Funext.fnEqToPointwise_symm_refl

/-! ## §3. Backward map round-trip. -/

#print axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl_forgetful
#print axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl_trivial

/-! ## §4. Kernel-meta correspondence. -/

#print axioms LeanFX2.Funext.kernelMetaCorrespondence_atRefl

/-! ## §5. Round-trip identity (rfl-fragment). -/

#print axioms LeanFX2.Funext.roundTripPathSide_refl
#print axioms LeanFX2.Funext.roundTripPointwiseSide_trivial
#print axioms LeanFX2.Funext.roundTripPointwiseSide_anyPointwise

/-! ## §6. Application laws. -/

#print axioms LeanFX2.Funext.applicationAtRefl
#print axioms LeanFX2.Funext.eqSubst_functionEquality
#print axioms LeanFX2.Funext.transport_at_pointwise_refl

end LeanFX2
