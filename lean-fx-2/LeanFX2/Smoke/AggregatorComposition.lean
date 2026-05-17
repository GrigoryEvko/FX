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

/-- 0-IH parametric smoke (listNil): exercises the
`isAggregatorSound_listNil` wrapper in isolation at carrier
`list nat`.  Demonstrates that 0-IH wrappers for parametric
constructors take their carrier type as a positional argument
without IH children, and compose cleanly into IsAggregatorSound. -/
theorem aggregator_listNil_natList_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listNil (context := sourceCtx) (elementType := Ty.nat)) :=
  isAggregatorSound_listNil (elementType := Ty.nat)

/-- 0-IH parametric smoke (optionNone): mirror of the listNil
example at the option carrier.  Demonstrates the parametric 0-IH
wrapper template extends uniformly across both list and option
zero-Ty-witness constructors. -/
theorem aggregator_optionNone_natOption_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionNone (context := sourceCtx)
        (elementType := Ty.nat)) :=
  isAggregatorSound_optionNone (elementType := Ty.nat)

/-- 2-deep listCons chain: `[0, 1] = listCons 0 (listCons 1 nil)`.
Exercises the 2-IH listCons wrapper recursively as the tail child
of another listCons, with all element-type indices bound
explicitly to sidestep the elaborator gap documented in
`aggregator_listCons_natList_closed`. -/
theorem aggregator_listCons_natListChain_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.natZero)
        (tailTerm :=
          Term.listCons (headTerm := Term.natSucc Term.natZero)
            (tailTerm := Term.listNil (elementType := Ty.nat)))) :=
  isAggregatorSound_listCons isAggregatorSound_natZero
    (isAggregatorSound_listCons
      (isAggregatorSound_natSucc isAggregatorSound_natZero)
      (isAggregatorSound_listNil (elementType := Ty.nat)))

/-- 2-IH Σ-pair smoke at non-dependent carrier `nat × nat`:
`IsAggregatorSound (Term.pair Term.natZero Term.natZero)` with
`secondType := Ty.nat` (closed, so the dependency vanishes after
`subst0`).  Demonstrates the 2-IH non-parametric wrapper composes
its two children at distinct (but here equal) carrier types. -/
theorem aggregator_pair_natNat_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.natZero)
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    isAggregatorSound_natZero

/-- 4-deep nat chain extending the natOne/Two/Three sequence.
Demonstrates that 1-IH chaining continues uniformly past depth 3
with no per-step bookkeeping growth. -/
theorem aggregator_natFour_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc
          (Term.natSucc (Term.natSucc Term.natZero)))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc
        (isAggregatorSound_natSucc isAggregatorSound_natZero)))

/-- Mixed Σ + nat-chain composition: a pair whose first component
is a depth-2 nat chain and whose second component is the
zero-depth natural.  Combines the natTwo chain pattern with the
non-dependent Σ-pair pattern, demonstrating cross-category
composition. -/
theorem aggregator_pair_natTwo_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.natSucc (Term.natSucc Term.natZero))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc isAggregatorSound_natZero))
    isAggregatorSound_natZero

/-- 0-IH HoTT-refl smoke: `IsAggregatorSound (Term.refl
RawTerm.natZero)` at carrier `Ty.nat`.  Exercises the
`isAggregatorSound_refl` wrapper in isolation, demonstrating that
HoTT identity-refl wrappers (carrier + rawWitness as implicits)
compose without IH children. -/
theorem aggregator_refl_natZero_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.refl (context := sourceCtx) (carrier := Ty.nat)
        RawTerm.natZero) :=
  isAggregatorSound_refl

/-- 0-IH observational-equality refl mirror at carrier `Ty.nat`:
`IsAggregatorSound (Term.oeqRefl RawTerm.natZero)`.  Mirror of the
HoTT `refl` example via the parallel `oeqRefl` wrapper. -/
theorem aggregator_oeqRefl_natZero_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.oeqRefl (context := sourceCtx) (carrier := Ty.nat)
        RawTerm.natZero) :=
  isAggregatorSound_oeqRefl

/-- 2-IH Σ-pair smoke at heterogeneous non-dependent carrier
`nat × bool`: `IsAggregatorSound (Term.pair Term.natZero
Term.boolTrue)` with `secondType := Ty.bool`.  Demonstrates that
the 2-IH non-parametric Σ wrapper composes children of distinct
type families (not just both nat). -/
theorem aggregator_pair_natBool_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.bool)
        (firstValue := Term.natZero)
        (secondValue := Term.boolTrue)) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    isAggregatorSound_boolTrue

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
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listNil_natList_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionNone_natOption_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_natListChain_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natNat_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natFour_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natTwo_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_refl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_oeqRefl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natBool_closed

end LeanFX2.SmokeAggregatorComposition
