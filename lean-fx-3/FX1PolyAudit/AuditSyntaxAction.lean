import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Action.Action
import FX1Poly.Axis.Term.Rename.RenameDefs
import FX1Poly.Axis.Term.Action.ActionInstances

/-! # FX1PolyAudit/AuditSyntaxAction — zero-axiom gate for the syntax action substrate

Persistent per-declaration `#assert_no_axioms` gate for the generic
renaming / action substrate now resident in `FX1Poly.Axis.Syntax`
(the modules relocated out of the deleted `Foundation` namespace).

This is the leaves-first native infra the PolyCell cell calculus stands
on: the universal `Action` typeclass with binding (Allais et al. ICFP'18)
and the positional `RawRenaming` Container with its `Action` instance.

The substrate carries only the positional / typeclass machinery that
PolyCell's `.mkGen`-cell `RawTerm` consumes — no coupling to an
intrinsic-MLTT raw term.
-/

-- Section 1: the universal Action typeclass + derived pointwise laws
#assert_no_axioms FX1Poly.Axis.Syntax.Action
#assert_no_axioms FX1Poly.Axis.Syntax.Action.compose_assoc
#assert_no_axioms FX1Poly.Axis.Syntax.Action.compose_identity_left
#assert_no_axioms FX1Poly.Axis.Syntax.Action.compose_identity_right

-- Section 2: the trivial IdAction smoke instance
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.identity
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.liftForTy
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.liftForRaw
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.compose
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.headIndex
#assert_no_axioms FX1Poly.Axis.Syntax.IdAction.composeAtHeadIndex

-- Section 3: dual-lift smoke over the mock type
#assert_no_axioms FX1Poly.Axis.Syntax.MockTy
#assert_no_axioms FX1Poly.Axis.Syntax.MockTy.act
#assert_no_axioms FX1Poly.Axis.Syntax.MockTy.act_identity_unit_smoke
#assert_no_axioms FX1Poly.Axis.Syntax.MockTy.act_identity_binderTy_smoke
#assert_no_axioms FX1Poly.Axis.Syntax.MockTy.act_identity_binderRaw_smoke

-- Section 4: positional RawRenaming Container + combinators
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.identity
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.lift
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.weaken
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.compose

-- Section 5: the Action RawRenaming instance equivalence theorems
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.identity_eq_action
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.lift_eq_actionForTy
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.lift_eq_actionForRaw
#assert_no_axioms FX1Poly.Axis.Syntax.RawRenaming.compose_eq_action
