import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.SubstActsOnTy

/-! # AuditMegaZ2A — Zero-axiom audit for the `Ty.act` recursion engine.

Tier 3 / MEGA-Z2.A ships:
* The `ActsOnRawTerm` typeclass (level-independent raw-term action)
* The `ActsOnTyVar` typeclass (level-specific variable lookup)
* `Ty.act` — the unified Tier 3 recursion engine over all 25 Ty
  constructors, parameterized by `[Action Container]`,
  `[ActsOnRawTerm Container]`, `[ActsOnTyVar Container level]`
* `ActsOnRawTerm` / `ActsOnTyVar` instances for `RawRenaming`
  (in `Foundation/Ty.lean`) and for `Subst level` (in
  `Foundation/SubstActsOnTy.lean`)
* Per-instance per-ctor `rfl`-bodied smoke theorems verifying that
  the `Ty.act` engine reduces correctly at leaf, recursive, binder,
  and raw-payload constructor positions.

Per the strict zero-axiom commitment in `CLAUDE.md`, every
declaration listed below must report "does not depend on any
axioms".  The audit gates auto-fire during `lake build LeanFX2`.

`RawTermSubst` is intentionally NOT instantiated — it cannot
sensibly act on `Ty.tyVar position` since `RawTermSubst`'s
`ActionTarget` is `RawTerm`, not `Ty level`.  Per the per-instance
analysis in `Foundation/Ty.lean`'s docstring, `RawTermSubst` will
later be wired through `RawTerm.act` (MEGA-Z4.A), not `Ty.act`.

`SubstHet` is also NOT instantiated here — heterogeneous-level
actions require a separate `ActsOnTyHet` typeclass for the
universe arm, which is a future phase (per Z1.B's SubstHet retreat
note).
-/

-- ============================================================
-- Section 1: Typeclass definitions
-- ============================================================

#print axioms LeanFX2.ActsOnRawTerm
#print axioms LeanFX2.ActsOnTyVar

-- ============================================================
-- Section 2: The `Ty.act` recursion engine
-- ============================================================

#print axioms LeanFX2.Ty.act

-- ============================================================
-- Section 3: Instances at `RawRenaming`
-- ============================================================

#print axioms LeanFX2.instActsOnRawTermRawRenaming
#print axioms LeanFX2.ActsOnTyVarOfRawRenaming

-- ============================================================
-- Section 4: Instances at `Subst level`
-- ============================================================

#print axioms LeanFX2.ActsOnRawTermOfSubst
#print axioms LeanFX2.ActsOnTyVarOfSubst

-- ============================================================
-- Section 5: Per-ctor smoke theorems on `RawRenaming`
-- ============================================================

#print axioms LeanFX2.Ty.act_rawRenaming_unit_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_tyVar_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_arrow_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_piTy_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_refine_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_id_smoke
#print axioms LeanFX2.Ty.act_rawRenaming_universe_smoke

-- ============================================================
-- Section 6: Per-ctor smoke theorems on `Subst level`
-- ============================================================

#print axioms LeanFX2.Ty.act_subst_unit_smoke
#print axioms LeanFX2.Ty.act_subst_tyVar_smoke
#print axioms LeanFX2.Ty.act_subst_arrow_smoke
#print axioms LeanFX2.Ty.act_subst_piTy_smoke
#print axioms LeanFX2.Ty.act_subst_refine_smoke
#print axioms LeanFX2.Ty.act_subst_id_smoke
#print axioms LeanFX2.Ty.act_subst_universe_smoke

-- ============================================================
-- Section 7: Typeclass resolution smoke
-- ============================================================
-- Verify Lean's typeclass synthesis finds the right instances at
-- the right `level`.  If resolution silently picked the wrong
-- instance, these `inferInstance` calls would fail to elaborate.

section TypeclassResolutionSmoke

open LeanFX2

example : ActsOnRawTerm RawRenaming := inferInstance
example (level : Nat) : ActsOnTyVar RawRenaming level := inferInstance
example (level : Nat) : ActsOnRawTerm (Subst level) := inferInstance
example (level : Nat) : ActsOnTyVar (Subst level) level := inferInstance

-- Resolution at the call site: applying `Ty.act` to a Ty + a
-- RawRenaming should typecheck without explicit instance arguments.
example {level scope targetScope : Nat}
    (someTy : Ty level scope) (someRenaming : RawRenaming scope targetScope) :
    Ty level targetScope :=
  someTy.act someRenaming

-- Same for `Subst level`.
example {level scope targetScope : Nat}
    (someTy : Ty level scope) (someSubst : Subst level scope targetScope) :
    Ty level targetScope :=
  someTy.act someSubst

end TypeclassResolutionSmoke

-- ============================================================
-- Section 8: Typeclass-method projections (sanity)
-- ============================================================

#print axioms LeanFX2.ActsOnRawTerm.actOnRawTerm
#print axioms LeanFX2.ActsOnTyVar.varToTy
