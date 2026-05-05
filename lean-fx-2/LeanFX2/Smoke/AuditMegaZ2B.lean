import LeanFX2.Foundation.TyActBridge

/-! # AuditMegaZ2B — Zero-axiom gates for `Ty.act` bridge theorems.

The load-bearing bridge definitions live in
`Foundation/TyActBridge.lean`.  This smoke module keeps the historical
MEGA-Z2.B audit surface while preventing production code from
depending on `LeanFX2.Smoke`.
-/

namespace LeanFX2.Smoke.AuditMegaZ2B

-- Bridge equivalence theorems (the headline Z2.B deliverable).
#print axioms LeanFX2.Ty.act_eq_rename
#print axioms LeanFX2.Ty.act_eq_subst
#print axioms LeanFX2.Ty.act_eq_weaken

-- Per-ctor definitional smokes.
#print axioms LeanFX2.Ty.act_subst_unit_def
#print axioms LeanFX2.Ty.act_subst_arrow_def
#print axioms LeanFX2.Ty.act_subst_piTy_def
#print axioms LeanFX2.Ty.act_subst_id_def
#print axioms LeanFX2.Ty.act_subst_universe_def

end LeanFX2.Smoke.AuditMegaZ2B
