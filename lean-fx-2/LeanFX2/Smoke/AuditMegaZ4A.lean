import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst

/-! # AuditMegaZ4A — Zero-axiom audit for the `RawTerm.act` engine.

Tier 3 / MEGA-Z4.A ships:
* The `ActsOnRawTermVar` typeclass (variable lookup at the raw layer)
  defined in `Foundation/RawTerm.lean`
* `RawTerm.act` — the Tier 3 recursion engine over all 56 RawTerm
  constructors, parameterized by `[Action Container]` and
  `[ActsOnRawTermVar Container]`
* `ActsOnRawTermVar` instances for `RawRenaming` (wraps renamed Fin
  back as `RawTerm.var`) and `RawTermSubst` (returns substituent
  RawTerm directly), shipped in `Foundation/RawSubst.lean`
* Per-instance per-ctor `rfl`-bodied smoke theorems verifying that
  the `RawTerm.act` engine reduces correctly at leaf, recursive,
  binder, and var constructor positions for both Containers — and
  identity-action smokes confirming `RawTerm.act t identity = t`.

Per the strict zero-axiom commitment in `CLAUDE.md`, every
declaration listed below must report "does not depend on any
axioms".  The audit gates auto-fire during `lake build LeanFX2`.

## Why no `Subst level` instance

`RawTerm.act` is the engine BEHIND `Foundation/Ty.lean`'s existing
`ActsOnRawTerm` typeclass.  Once Z4.B (the redirect milestone)
fold's `RawTerm.rename` / `RawTerm.subst` to use `RawTerm.act`,
the `ActsOnRawTerm` instances for `RawRenaming` (in `Foundation/
Ty.lean:811`) and `Subst level` (in
`Foundation/SubstActsOnTy.lean:43`) will route through this engine
automatically.  Z4.A intentionally does NOT redirect — it ships the
engine + the two raw-side instances (RawRenaming, RawTermSubst) as
the FOUNDATION step, and leaves the redirect to a separate phase.

## Why no `SubstHet` instance

Heterogeneous-level actions (`SubstHet`) require additional
machinery for the universe arm of `Ty.act` and would be a future
phase, mirroring the SubstHet retreat note from Z1.B / Z2.A.
`RawTerm.act` does not depend on SubstHet at all — the raw layer
is level-independent.
-/

-- ============================================================
-- Section 1: Typeclass definition
-- ============================================================

#print axioms LeanFX2.ActsOnRawTermVar
#print axioms LeanFX2.ActsOnRawTermVar.varToRawTerm

-- ============================================================
-- Section 2: The `RawTerm.act` recursion engine
-- ============================================================

#print axioms LeanFX2.RawTerm.act

-- ============================================================
-- Section 3: Instance at `RawRenaming`
-- ============================================================

#print axioms LeanFX2.instActsOnRawTermVarRawRenaming

-- ============================================================
-- Section 4: Instance at `RawTermSubst`
-- ============================================================

#print axioms LeanFX2.instActsOnRawTermVarRawTermSubst

-- ============================================================
-- Section 5: Per-ctor smoke theorems on `RawRenaming`
-- ============================================================

#print axioms LeanFX2.RawTerm.act_rawRenaming_unit_smoke
#print axioms LeanFX2.RawTerm.act_rawRenaming_var_smoke
#print axioms LeanFX2.RawTerm.act_rawRenaming_app_smoke
#print axioms LeanFX2.RawTerm.act_rawRenaming_lam_smoke
#print axioms LeanFX2.RawTerm.act_rawRenaming_pathLam_smoke
#print axioms LeanFX2.RawTerm.act_rawRenaming_universeCode_smoke

-- ============================================================
-- Section 6: Per-ctor smoke theorems on `RawTermSubst`
-- ============================================================

#print axioms LeanFX2.RawTerm.act_rawTermSubst_unit_smoke
#print axioms LeanFX2.RawTerm.act_rawTermSubst_var_smoke
#print axioms LeanFX2.RawTerm.act_rawTermSubst_app_smoke
#print axioms LeanFX2.RawTerm.act_rawTermSubst_lam_smoke
#print axioms LeanFX2.RawTerm.act_rawTermSubst_pathLam_smoke
#print axioms LeanFX2.RawTerm.act_rawTermSubst_universeCode_smoke

-- ============================================================
-- Section 7: Identity-action smokes (RawTerm.act t identity = t)
-- ============================================================

#print axioms LeanFX2.RawTerm.act_identity_rawRenaming_unit_smoke
#print axioms LeanFX2.RawTerm.act_identity_rawTermSubst_unit_smoke
#print axioms LeanFX2.RawTerm.act_identity_rawRenaming_var_smoke
#print axioms LeanFX2.RawTerm.act_identity_rawTermSubst_var_smoke

-- ============================================================
-- Section 8: Typeclass resolution smoke
-- ============================================================
-- Verify Lean's typeclass synthesis finds the right instances at
-- the call site.  If resolution silently picked the wrong instance,
-- these `inferInstance` calls would fail to elaborate.

section TypeclassResolutionSmoke

open LeanFX2

example : ActsOnRawTermVar RawRenaming := inferInstance
example : ActsOnRawTermVar RawTermSubst := inferInstance

-- Resolution at the call site: applying `RawTerm.act` to a RawTerm
-- + a RawRenaming should typecheck without explicit instance args.
example {sourceScope targetScope : Nat}
    (someRaw : RawTerm sourceScope)
    (someRenaming : RawRenaming sourceScope targetScope) :
    RawTerm targetScope :=
  someRaw.act someRenaming

-- Same for `RawTermSubst`.
example {sourceScope targetScope : Nat}
    (someRaw : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope) :
    RawTerm targetScope :=
  someRaw.act sigma

end TypeclassResolutionSmoke
