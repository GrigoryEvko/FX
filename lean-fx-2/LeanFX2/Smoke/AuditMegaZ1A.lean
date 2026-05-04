import LeanFX2.Foundation.Action

/-! # AuditMegaZ1A — Zero-axiom audit for the Action typeclass framework.

Tier 3 / MEGA-Z1.A shipped `LeanFX2/Foundation/Action.lean`:
* The `Action` typeclass with dual-lift (`liftForTy` + `liftForRaw`)
* Pointwise typeclass laws (compose_assoc, identity left/right, headIndex_compose)
* Derived `Action.compose_assoc`, `Action.compose_identity_left`,
  `Action.compose_identity_right` theorems
* The `IdAction` smoke-test instance + its instance witness
* The `MockTy` 3-ctor mock + `MockTy.act` recursion engine
* Three smoke-test theorems exercising dual-lift through MockTy.act

Per the strict zero-axiom commitment in `CLAUDE.md`, every declaration
listed below must report "does not depend on any axioms".  The audit
gates auto-fire during `lake build LeanFX2`.

If any declaration prints `propext`, `Quot.sound`, `Classical.choice`,
or any user-declared axiom, the audit FAILS and the framework is NOT
shipped — fix the leak or delete the declaration.
-/

-- The typeclass definition itself
#print axioms LeanFX2.Action

-- Derived theorems (consumer-facing, used by Z2+ recursion engines)
#print axioms LeanFX2.Action.compose_assoc
#print axioms LeanFX2.Action.compose_identity_left
#print axioms LeanFX2.Action.compose_identity_right

-- IdAction smoke-test instance and its operations
#print axioms LeanFX2.IdAction
#print axioms LeanFX2.IdAction.identity
#print axioms LeanFX2.IdAction.liftForTy
#print axioms LeanFX2.IdAction.liftForRaw
#print axioms LeanFX2.IdAction.compose
#print axioms LeanFX2.IdAction.headIndex
#print axioms LeanFX2.IdAction.composeAtHeadIndex

-- The instance witness for IdAction
#print axioms LeanFX2.instActionIdAction

-- MockTy and its recursion engine (validates dual-lift design)
#print axioms LeanFX2.MockTy
#print axioms LeanFX2.MockTy.act

-- Smoke-test theorems exercising MockTy.act + IdAction.identity
#print axioms LeanFX2.MockTy.act_identity_unit_smoke
#print axioms LeanFX2.MockTy.act_identity_binderTy_smoke
#print axioms LeanFX2.MockTy.act_identity_binderRaw_smoke

-- Typeclass field projections (each field of `Action` declared above
-- becomes a projection function once the class compiles; these audit
-- gates verify no propext leak from class-elab machinery).
#print axioms LeanFX2.Action.headIndex
#print axioms LeanFX2.Action.liftForTy
#print axioms LeanFX2.Action.liftForRaw
#print axioms LeanFX2.Action.identity
#print axioms LeanFX2.Action.compose
#print axioms LeanFX2.Action.composeAtHeadIndex
#print axioms LeanFX2.Action.compose_assoc_pointwise
#print axioms LeanFX2.Action.compose_identity_left_pointwise
#print axioms LeanFX2.Action.compose_identity_right_pointwise
#print axioms LeanFX2.Action.headIndex_compose
