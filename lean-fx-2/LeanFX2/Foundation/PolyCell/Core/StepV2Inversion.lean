import LeanFX2.Foundation.PolyCell.Core.StepV2

/-! # Foundation/PolyCell/Core/StepV2Inversion — Step inversion lemmas

V2-L3.1 phase C step 6 prep (2026-05-27).  Ships foundational
inversion lemmas the SR theorem's cong arm will consume.

## What inversion lemmas are

When the SR theorem proceeds by case analysis on `Step source
target`, each arm needs to know what's structurally possible.
For terminal terms (units, leaf constructors with empty children
spine), the inversion is "Step is impossible" -- no rule fires.
For non-leaf terms, inversion characterizes the possible source/
target shapes per Step constructor.

This file builds inversion bottom-up: empty-spine → leaf-ctors →
specific-redex inversions (deferred to later iterations).

## What this file ships (phase C step 6 prep)

* `StepChildren.no_step_at_empty_spine` -- StepChildren is
  uninhabited when the input children spine is `.childNil`.
  Foundational because the `cong` arm of any leaf-ctor Step
  inversion needs this fact.

* `Step.no_step_from_unit` -- the unit term admits no Step.
  Direct application of the empty-spine lemma to the cong arm,
  combined with auto-discharge of the other 17 Step constructors
  (their source patterns require generators other than gen_unit).

## What this file does NOT ship (yet)

* Inversion lemmas for non-leaf terms (boolElim, lam, app, etc.)
  -- these characterize which Step ctor could have fired given
  the source shape.  Deferred to later phase C step 6 atomic
  iterations.
* The full SR theorem itself.  Built atop these inversion lemmas
  + V2-L2.12's cell-level subst boundary + the certifier's
  recursive structure.

## Zero-axiom verification

Both shipped declarations pass `#assert_no_axioms`.  Audit-gated
in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **StepChildren has no inhabitants at an empty spine.**

`StepChildren` has two constructors (`.here` and `.there`), and
BOTH require the input spine to be a `.childCons` (they pattern-
match on a head-and-tail decomposition).  Neither matches the
`.childNil` input shape, so `StepChildren .childNil _` is
uninhabited.

This is the foundational lemma the cong arm of every leaf-ctor
inversion consumes: when reducing under a generator with an empty
children spine (like `gen_unit`, `gen_boolTrue`, etc.), the cong
rule cannot fire because there's nowhere for the inner Step to
sit.

Proof: `intro h; cases h` -- Lean's `cases` tactic recognizes
neither constructor pattern matches `.childNil` and discharges
the goal automatically. -/
theorem StepChildren.no_step_at_empty_spine
    {parentScope : Nat}
    {children' : RawTermChildrenV2 [] parentScope} :
    ¬ StepChildren
        (RawTermChildrenV2.childNil : RawTermChildrenV2 [] parentScope)
        children' := by
  intro witness
  cases witness

/-- **The unit term admits no Step reduction.**

`(.mkGen .gen_unit () .childNil)` is a leaf term: 0-arity
constructor, empty children spine, no eliminator that fires on
it.  None of `Step`'s 18 constructors can reduce it:

* `beta` requires source generator `gen_app` -- mismatch.
* Iota constructors require specific eliminators (`gen_boolElim`,
  `gen_fst`, etc.) -- all mismatch `gen_unit`.
* `cong` requires a `StepChildren` over the children spine.  The
  spine here is `.childNil`, and
  `StepChildren.no_step_at_empty_spine` shows that's uninhabited.

Lean's `cases` tactic discharges the 17 mismatched-generator
cases automatically via index unification failure.  Only the cong
case needs explicit handling, which routes through the empty-
spine lemma above.

This is the SIMPLEST Step inversion result: a leaf term blocks
all reduction.  Future inversions will be more complex
(non-leaf terms admit specific Step ctors, and the inversion
characterizes which). -/
theorem Step.no_step_from_unit
    {scope : Nat} {target : RawTermV2 scope} :
    ¬ Step (.mkGen .gen_unit () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

end LeanFX2.Foundation.PolyCell.Core
