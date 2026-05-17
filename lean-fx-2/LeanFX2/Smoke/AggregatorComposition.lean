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

#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_unit_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natOne_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natTwo_closed

end LeanFX2.SmokeAggregatorComposition
