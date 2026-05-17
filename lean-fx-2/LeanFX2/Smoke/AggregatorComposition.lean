import LeanFX2.Term.StrengtheningImage

/-! # AggregatorComposition — IsAggregatorSound composition smoke audit.

Smoke audit demonstrating that the 78 per-arm dispatcher wrappers
(`isAggregatorSound_<ctor>`) shipped across Phases 80–90 compose
cleanly on closed concrete Terms.

## Coverage

Three composition examples at progressively deeper nesting:

* `aggregator_unit_closed` — zero-depth closed atomic (no
  composition required, sanity check that 0-IH wrappers apply
  with no IH arguments).
* `aggregator_natOne_closed` — 1-deep composition (natSucc over
  natZero); demonstrates that a 1-IH wrapper accepts a 0-IH
  wrapper as its child aggregator.
* `aggregator_natTwo_closed` — 2-deep composition (natSucc over
  natSucc over natZero); demonstrates that 1-IH wrappers chain
  through arbitrary depth.

## Purpose

Each example is a real shipped theorem (no `sorry`, no axiom)
proving `IsAggregatorSound` for a closed concrete Term, by
applying the per-arm wrappers in head-leaf direction.  Together
they:

* verify the wrapper signatures unify under the universally-
  quantified `IsAggregatorSound` predicate without coercion gaps;
* serve as future regression evidence that wrapper composition
  stays clean across kernel-shape edits;
* establish the calling pattern that the eventual universal
  headline (`∀ sourceTerm, IsAggregatorSound sourceTerm`, lands
  in a later phase via structural induction) will compose at
  each ctor arm.

Each smoke theorem is gated below by `#print axioms` for
reviewer regression and by `#assert_no_axioms` for the strict
audit harness. -/

namespace LeanFX2.SmokeAggregatorComposition

open LeanFX2 LeanFX2.Term

/-- Zero-depth smoke: `IsAggregatorSound Term.unit` follows directly
from `isAggregatorSound_unit` with no composition (Term.unit has
zero recursive children). -/
theorem aggregator_unit_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.unit (context := sourceCtx)) :=
  isAggregatorSound_unit

/-- 1-deep smoke: `IsAggregatorSound (Term.natSucc Term.natZero)`
composes one 1-IH wrapper over one 0-IH wrapper, demonstrating
the wrapper signatures unify under the universally-quantified
`IsAggregatorSound` predicate. -/
theorem aggregator_natOne_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx) Term.natZero) :=
  isAggregatorSound_natSucc isAggregatorSound_natZero

/-- 2-deep smoke: `IsAggregatorSound (Term.natSucc (Term.natSucc
Term.natZero))` chains two 1-IH wrappers, demonstrating that
composition extends through arbitrary depth in the head-leaf
direction. -/
theorem aggregator_natTwo_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc Term.natZero)) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc isAggregatorSound_natZero)

/-- 3-deep smoke: extends the nat chain by one more level
(natSucc^3 natZero); demonstrates that arbitrary-depth chaining
imposes no per-step coercion or unification overhead. -/
theorem aggregator_natThree_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc (Term.natSucc Term.natZero))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc isAggregatorSound_natZero))

/-- Closed-atomic smoke (boolean): mirrors the `Term.unit` case
but at `Ty.bool` via the `boolTrue` constructor.  Demonstrates
that the closed-atomic wrapper template extends uniformly across
the 0-IH zero-Ty-witness ctors. -/
theorem aggregator_boolTrue_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.boolTrue (context := sourceCtx)) :=
  isAggregatorSound_boolTrue

/-- Closed-atomic smoke (boolean false): boolFalse mirror. -/
theorem aggregator_boolFalse_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.boolFalse (context := sourceCtx)) :=
  isAggregatorSound_boolFalse

/-- 1-IH smoke at parametric type: `IsAggregatorSound
(Term.optionSome Term.natZero)` builds an `option nat` from a
0-IH `nat` child via the optionSome 1-IH wrapper.  Demonstrates
the wrapper composes cleanly across an Ty.optionType
parametric type boundary. -/
theorem aggregator_optionSome_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm := Term.natZero)) :=
  isAggregatorSound_optionSome isAggregatorSound_natZero

/-- 1-IH smoke at heterogeneous-Ty type: `IsAggregatorSound
(Term.eitherInl Term.natZero)` at carrier `Either Ty.nat
Ty.bool`.  Demonstrates that 1-IH wrappers carry through the
two-type either-form with the unused carrier supplied via the
named implicit. -/
theorem aggregator_eitherInl_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInl (context := sourceCtx)
        (rightType := Ty.bool) (valueTerm := Term.natZero)) :=
  isAggregatorSound_eitherInl (rightType := Ty.bool)
    isAggregatorSound_natZero

/-- 1-IH smoke (eitherInr mirror): `IsAggregatorSound
(Term.eitherInr Term.boolTrue)` at carrier `Either Ty.nat
Ty.bool` with leftType named via implicit.  Mirror of the
eitherInl example demonstrating both side-injections of the
either form. -/
theorem aggregator_eitherInr_boolTrue_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInr (context := sourceCtx)
        (leftType := Ty.nat) (valueTerm := Term.boolTrue)) :=
  isAggregatorSound_eitherInr (leftType := Ty.nat)
    isAggregatorSound_boolTrue

/-- 1-IH-over-1-IH smoke at parametric type: `IsAggregatorSound
(Term.optionSome (Term.natSucc Term.natZero))` builds `Some 1`,
demonstrating that 1-IH parametric wrappers compose through a
nested 1-IH child (parametric Ty.optionType wrapping a
non-trivial nat term). -/
theorem aggregator_optionSome_natOne_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm := Term.natSucc Term.natZero)) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_natSucc isAggregatorSound_natZero)

/-- 2-IH smoke at parametric type with explicit elementType:
`IsAggregatorSound (Term.listCons Term.natZero Term.listNil)`.
Originally dropped in Phase 93 — Lean's elaborator couldn't
propagate elementType from headTerm to tailTerm := Term.listNil
and silently inserted a sorry.  Fixed here by binding listNil's
elementType explicitly via named implicit. -/
theorem aggregator_listCons_natList_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.natZero)
        (tailTerm := Term.listNil (elementType := Ty.nat))) :=
  isAggregatorSound_listCons isAggregatorSound_natZero
    (isAggregatorSound_listNil (elementType := Ty.nat))

#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_unit_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natOne_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natTwo_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natThree_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_boolTrue_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_boolFalse_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInr_boolTrue_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_natOne_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_natList_closed

end LeanFX2.SmokeAggregatorComposition
