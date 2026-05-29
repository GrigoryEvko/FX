import FX1PolyAudit.DependencyAudit
import FX1Poly.Foundation.Action
import FX1Poly.Foundation.RawSubst.RenameDefs
import FX1Poly.Foundation.RawSubst.ActionInstances

/-! # FX1PolyAudit/AuditFoundation — zero-axiom gate for the native infra

Persistent per-declaration `#assert_no_axioms` gate for the generic
renaming / action substrate migrated out of lean-fx-2's
`LeanFX2.Foundation.{Action, RawSubst.RenameDefs, RawSubst.ActionInstances}`.

This is the leaves-first native infra the PolyCell cell calculus stands
on: the universal `Action` typeclass with binding (Allais et al. ICFP'18)
and the positional `RawRenaming` Container with its `Action` instance.

The clean cut SEVERED the legacy MLTT `RawTerm` coupling: the lean-fx-2
originals dragged `Foundation.RawTerm` (the intrinsic-MLTT raw term);
these native copies carry only the positional / typeclass machinery that
PolyCell's `.mkGen`-cell `RawTerm` actually consumes.
-/

-- Section 1: the universal Action typeclass + derived pointwise laws
#assert_no_axioms FX1Poly.Foundation.Action
#assert_no_axioms FX1Poly.Foundation.Action.compose_assoc
#assert_no_axioms FX1Poly.Foundation.Action.compose_identity_left
#assert_no_axioms FX1Poly.Foundation.Action.compose_identity_right

-- Section 2: the trivial IdAction smoke instance
#assert_no_axioms FX1Poly.Foundation.IdAction
#assert_no_axioms FX1Poly.Foundation.IdAction.identity
#assert_no_axioms FX1Poly.Foundation.IdAction.liftForTy
#assert_no_axioms FX1Poly.Foundation.IdAction.liftForRaw
#assert_no_axioms FX1Poly.Foundation.IdAction.compose
#assert_no_axioms FX1Poly.Foundation.IdAction.headIndex
#assert_no_axioms FX1Poly.Foundation.IdAction.composeAtHeadIndex

-- Section 3: dual-lift smoke over the mock type
#assert_no_axioms FX1Poly.Foundation.MockTy
#assert_no_axioms FX1Poly.Foundation.MockTy.act
#assert_no_axioms FX1Poly.Foundation.MockTy.act_identity_unit_smoke
#assert_no_axioms FX1Poly.Foundation.MockTy.act_identity_binderTy_smoke
#assert_no_axioms FX1Poly.Foundation.MockTy.act_identity_binderRaw_smoke

-- Section 4: positional RawRenaming Container + combinators
#assert_no_axioms FX1Poly.Foundation.RawRenaming
#assert_no_axioms FX1Poly.Foundation.RawRenaming.identity
#assert_no_axioms FX1Poly.Foundation.RawRenaming.lift
#assert_no_axioms FX1Poly.Foundation.RawRenaming.weaken
#assert_no_axioms FX1Poly.Foundation.RawRenaming.compose

-- Section 5: the Action RawRenaming instance equivalence theorems
#assert_no_axioms FX1Poly.Foundation.RawRenaming.identity_eq_action
#assert_no_axioms FX1Poly.Foundation.RawRenaming.lift_eq_actionForTy
#assert_no_axioms FX1Poly.Foundation.RawRenaming.lift_eq_actionForRaw
#assert_no_axioms FX1Poly.Foundation.RawRenaming.compose_eq_action
