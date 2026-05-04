import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Subst

/-! # AuditMegaZ1B — Zero-axiom audit for the Action typeclass instances.

Tier 3 / MEGA-Z1.B wraps the existing substitution machinery as
concrete `Action` typeclass instances supplied by Z1.A.  Per the
brief (and the SubstHet retreat noted in the report), this audit
covers THREE instances:

1. `instance : Action RawRenaming`
2. `instance : Action RawTermSubst`
3. `instance (level : Nat) : Action (Subst level)`

The `Action SubstHet` instance is intentionally OMITTED — `SubstHet`'s
cumulOk witness threading does not collapse to a self-composition
under fixed `(sourceLevel, targetLevel)`.  Specifically:

* `SubstHet sourceLevel targetLevel src tgt` has `forTy : Fin src →
  Ty targetLevel tgt`, but composing two `SubstHet`s at the same
  `(sourceLevel, targetLevel)` would require substituting a
  `Ty targetLevel mid` against a `SubstHet sourceLevel targetLevel mid
  tgt`, whose `Ty.substHet` only consumes `Ty sourceLevel _`.
* `SubstHet.identity` requires `cumulOk : sourceLevel ≤ targetLevel`,
  which is propositional data not auto-resolvable by typeclass
  inference at the diagonal `sourceLevel ≠ targetLevel`.

The natural compositions for `SubstHet` are `Subst.composeSubstHet`
and `SubstHet.composeSubst` (which already exist in `SubstHet.lean`),
NOT a self-compose — these are heterogeneous-bridge operations that
warrant their own typeclass treatment in a future Tier-3 phase, NOT
shoehorning into `Action`.

Per the strict zero-axiom commitment in `CLAUDE.md`, every
declaration listed below must report "does not depend on any
axioms".  The audit gates auto-fire during `lake build LeanFX2`.
-/

-- ============================================================
-- Instance 1: Action RawRenaming
-- ============================================================

#print axioms LeanFX2.instActionRawRenaming

-- Equivalence theorems for RawRenaming
#print axioms LeanFX2.RawRenaming.identity_eq_action
#print axioms LeanFX2.RawRenaming.lift_eq_actionForTy
#print axioms LeanFX2.RawRenaming.lift_eq_actionForRaw
#print axioms LeanFX2.RawRenaming.compose_eq_action

-- ============================================================
-- Instance 2: Action RawTermSubst
-- ============================================================

#print axioms LeanFX2.instActionRawTermSubst

-- Equivalence theorems for RawTermSubst
#print axioms LeanFX2.RawTermSubst.identity_eq_action
#print axioms LeanFX2.RawTermSubst.lift_eq_actionForTy
#print axioms LeanFX2.RawTermSubst.lift_eq_actionForRaw
#print axioms LeanFX2.RawTermSubst.compose_eq_action

-- ============================================================
-- Instance 3: Action (Subst level)
-- ============================================================

#print axioms LeanFX2.instActionSubst

-- Equivalence theorems for Subst
#print axioms LeanFX2.Subst.identity_eq_action
#print axioms LeanFX2.Subst.lift_eq_actionForTy
#print axioms LeanFX2.Subst.lift_eq_actionForRaw
#print axioms LeanFX2.Subst.compose_eq_action

-- ============================================================
-- Smoke: derived `Action.compose_assoc` etc. inhabited at instances
-- ============================================================

-- These #check calls verify typeclass resolution finds each instance.
-- If resolution silently picked the wrong instance (e.g., IdAction
-- instead of RawRenaming), these would fail to elaborate.

section TypeclassResolutionSmoke

open LeanFX2

example : Action RawRenaming := inferInstance
example : Action RawTermSubst := inferInstance
example (level : Nat) : Action (Subst level) := inferInstance

end TypeclassResolutionSmoke

-- ============================================================
-- Action class field projections used by the new instances
-- (already audited in AuditMegaZ1A but re-verified here for
-- per-instance evidence of clean resolution)
-- ============================================================

#print axioms LeanFX2.Action.headIndex
#print axioms LeanFX2.Action.compose
#print axioms LeanFX2.Action.identity
#print axioms LeanFX2.Action.liftForTy
#print axioms LeanFX2.Action.liftForRaw
#print axioms LeanFX2.Action.composeAtHeadIndex

-- Derived theorems exercised through these instances
#print axioms LeanFX2.Action.compose_assoc
#print axioms LeanFX2.Action.compose_identity_left
#print axioms LeanFX2.Action.compose_identity_right
