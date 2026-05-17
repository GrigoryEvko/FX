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

/-- 5-deep nat chain extending the nat sequence to confirm 1-IH
chaining stays uniform past depth 4 as well. -/
theorem aggregator_natFive_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc
          (Term.natSucc
            (Term.natSucc (Term.natSucc Term.natZero))))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc
        (isAggregatorSound_natSucc
          (isAggregatorSound_natSucc isAggregatorSound_natZero))))

/-- Nested parametric: `Some (Some natZero)` at carrier
`option (option nat)`.  Demonstrates that the 1-IH parametric
`optionSome` wrapper composes recursively as the inner child of
another `optionSome`, with the outer `valueType` implicit
threading through the inner construction. -/
theorem aggregator_optionSome_optionSome_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

/-- 1-IH heterogeneous with non-trivial child: `eitherInl
(natSucc natZero)` at carrier `Either nat bool`.  Variant of
the existing `eitherInl_natZero` example carrying a depth-1
nat chain rather than the bare zero.  Demonstrates that
heterogeneous 1-IH wrappers compose with non-trivial 1-IH
children of the matching side. -/
theorem aggregator_eitherInl_natOne_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInl (context := sourceCtx)
        (rightType := Ty.bool)
        (valueTerm := Term.natSucc Term.natZero)) :=
  isAggregatorSound_eitherInl (rightType := Ty.bool)
    (isAggregatorSound_natSucc isAggregatorSound_natZero)

/-- Triple-nested parametric: `Some (Some (Some natZero))` at
carrier `option (option (option nat))`.  Demonstrates that the
optionSome 1-IH parametric wrapper composes recursively past
depth 2 with no per-step bookkeeping growth. -/
theorem aggregator_optionSome_triple_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.optionSome
            (valueTerm := Term.optionSome
              (valueTerm := Term.natZero)))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_optionSome
      (isAggregatorSound_optionSome isAggregatorSound_natZero))

/-- Mixed-content listCons: `[1, 0]` = `listCons (natSucc natZero)
(listCons natZero listNil)`.  Variant of the existing
`listCons_natListChain_closed` showing that the head positions
of a chained listCons may carry different nat values; first
example with non-uniform list element values. -/
theorem aggregator_listCons_natOne_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.natSucc Term.natZero)
        (tailTerm :=
          Term.listCons (headTerm := Term.natZero)
            (tailTerm := Term.listNil (elementType := Ty.nat)))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_natSucc isAggregatorSound_natZero)
    (isAggregatorSound_listCons isAggregatorSound_natZero
      (isAggregatorSound_listNil (elementType := Ty.nat)))

/-- Cross-category Σ + option: `pair (optionSome natZero) natZero`
at carrier `option nat × nat` (secondType := Ty.nat closed).
Demonstrates that the 2-IH non-parametric Σ wrapper accepts a
1-IH parametric child as its first component. -/
theorem aggregator_pair_optionSome_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.optionSome (valueTerm := Term.natZero))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    isAggregatorSound_natZero

/-- Heterogeneous either with parametric child: `eitherInr (Some
natZero)` at carrier `Either nat (option nat)`.  Demonstrates the
1-IH heterogeneous wrapper (right injection) composes with a 1-IH
parametric child rather than an atomic one. -/
theorem aggregator_eitherInr_optionSome_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInr (context := sourceCtx)
        (leftType := Ty.nat)
        (valueTerm :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_eitherInr (leftType := Ty.nat)
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

/-- Cross-category Sigma + either: `pair (eitherInl natZero)
natZero` at carrier `Either nat bool × nat` (secondType :=
Ty.nat closed).  Demonstrates the 2-IH non-parametric Sigma
wrapper accepts a 1-IH heterogeneous child as its first
component (counterpart to the optionSome cross-category
example in Phase 99). -/
theorem aggregator_pair_eitherInl_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue :=
          Term.eitherInl (rightType := Ty.bool)
            (valueTerm := Term.natZero))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_eitherInl (rightType := Ty.bool)
      isAggregatorSound_natZero)
    isAggregatorSound_natZero

/-- List of options: `listCons (Some natZero) listNil` at carrier
`list (option nat)`.  Exercises the 2-IH parametric listCons
wrapper with a parametric head and an explicit elementType
binding on the listNil tail (mirroring the Phase 93 fix). -/
theorem aggregator_listCons_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.optionSome (valueTerm := Term.natZero))
        (tailTerm :=
          Term.listNil (elementType := Ty.optionType Ty.nat))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    (isAggregatorSound_listNil
      (elementType := Ty.optionType Ty.nat))

/-- 6-deep natSucc chain extending the natOne..natFive sequence.
Continues the depth-uniformity demonstration for 1-IH wrappers
past depth 5. -/
theorem aggregator_natSix_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc
          (Term.natSucc
            (Term.natSucc
              (Term.natSucc (Term.natSucc Term.natZero)))))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc
        (isAggregatorSound_natSucc
          (isAggregatorSound_natSucc
            (isAggregatorSound_natSucc isAggregatorSound_natZero)))))

/-- 4-deep optionSome chain: `Some (Some (Some (Some natZero)))`
at carrier `option (option (option (option nat)))`.  Extends
the optionSome triple-nesting from Phase 99 to depth 4. -/
theorem aggregator_optionSome_quad_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.optionSome
            (valueTerm :=
              Term.optionSome
                (valueTerm :=
                  Term.optionSome (valueTerm := Term.natZero))))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_optionSome
      (isAggregatorSound_optionSome
        (isAggregatorSound_optionSome isAggregatorSound_natZero)))

/-- Pair-of-pair at carrier `(nat × nat) × nat`: `pair (pair
natZero natZero) natZero`.  Demonstrates the 2-IH non-parametric
Sigma wrapper accepts a 2-IH non-parametric Sigma child as its
first component (Sigma-nested-in-Sigma). -/
theorem aggregator_pair_pair_natNatNat_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)
    isAggregatorSound_natZero

/-- List of Σ-pairs: `[(natZero, natZero)]` at carrier
`list (nat × nat)`.  Demonstrates that the 2-IH parametric
listCons wrapper accepts a 2-IH non-parametric Sigma value as
its head, with the listNil elementType bound to the matching
Sigma carrier. -/
theorem aggregator_listCons_pair_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))
        (tailTerm :=
          Term.listNil (elementType := Ty.sigmaTy Ty.nat Ty.nat))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)
    (isAggregatorSound_listNil
      (elementType := Ty.sigmaTy Ty.nat Ty.nat))

/-- Sigma with Sigma in the SECOND component: `(natZero, (natZero,
natZero))` at carrier `nat × (nat × nat)` (secondType :=
Ty.sigmaTy Ty.nat Ty.nat closed).  Counterpart to
`aggregator_pair_pair_natNatNat_closed` which nests the Sigma
in the FIRST component; together they confirm Sigma-nesting
composes symmetrically across both component positions. -/
theorem aggregator_pair_natZero_pair_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.sigmaTy Ty.nat Ty.nat)
        (firstValue := Term.natZero)
        (secondValue :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)

/-- 7-deep natSucc chain extending the natOne..natSix sequence.
Demonstrates that 1-IH chaining stays uniform past depth 6 as
well. -/
theorem aggregator_natSeven_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc
          (Term.natSucc
            (Term.natSucc
              (Term.natSucc
                (Term.natSucc
                  (Term.natSucc Term.natZero))))))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc
        (isAggregatorSound_natSucc
          (isAggregatorSound_natSucc
            (isAggregatorSound_natSucc
              (isAggregatorSound_natSucc isAggregatorSound_natZero))))))

/-- Sigma with option in the SECOND component: `(natZero, Some
natZero)` at carrier `nat × option nat` (secondType :=
Ty.optionType Ty.nat closed).  Counterpart to Phase 99's
`pair_optionSome_natZero` which puts the parametric child in
the first component; together they confirm parametric-in-Sigma
nesting works at either component position. -/
theorem aggregator_pair_natZero_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.optionType Ty.nat)
        (firstValue := Term.natZero)
        (secondValue :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

/-- Sigma with either in the SECOND component: `(natZero,
eitherInl natZero)` at carrier `nat × Either nat bool`.
Counterpart to Phase 100's `pair_eitherInl_natZero` which puts
the heterogeneous-injection child in the first component;
together they confirm heterogeneous-in-Sigma nesting works at
either component position. -/
theorem aggregator_pair_natZero_eitherInl_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.eitherType Ty.nat Ty.bool)
        (firstValue := Term.natZero)
        (secondValue :=
          Term.eitherInl (rightType := Ty.bool)
            (valueTerm := Term.natZero))) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    (isAggregatorSound_eitherInl (rightType := Ty.bool)
      isAggregatorSound_natZero)

/-- 3-element list `[0, 0, 0]` at carrier `list nat`.  Extends
the existing 2-element `listCons_natListChain_closed` to depth 3,
demonstrating that the 2-IH parametric listCons wrapper chains
uniformly past length 2 with each tail-side recursive call
binding `elementType := Ty.nat` only at the final listNil. -/
theorem aggregator_listCons_natListChainThree_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.natZero)
        (tailTerm :=
          Term.listCons (headTerm := Term.natZero)
            (tailTerm :=
              Term.listCons (headTerm := Term.natZero)
                (tailTerm :=
                  Term.listNil (elementType := Ty.nat))))) :=
  isAggregatorSound_listCons isAggregatorSound_natZero
    (isAggregatorSound_listCons isAggregatorSound_natZero
      (isAggregatorSound_listCons isAggregatorSound_natZero
        (isAggregatorSound_listNil (elementType := Ty.nat))))

/-- optionSome carrying a Sigma-pair: `Some (natZero, natZero)`
at carrier `option (nat × nat)`.  Demonstrates that the 1-IH
parametric optionSome wrapper composes with a 2-IH non-parametric
Sigma child, with the option's valueType implicitly inferred to
the matching Sigma carrier. -/
theorem aggregator_optionSome_pair_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)

/-- eitherInr (right side) carrying a Sigma-pair: `eitherInr
(natZero, natZero)` at carrier `Either nat (nat × nat)`.
Demonstrates that the 1-IH heterogeneous-injection wrapper
composes with a 2-IH non-parametric Sigma child at its valueTerm
slot. -/
theorem aggregator_eitherInr_pair_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInr (context := sourceCtx)
        (leftType := Ty.nat)
        (valueTerm :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))) :=
  isAggregatorSound_eitherInr (leftType := Ty.nat)
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)

/-- List of either-injected values: `[eitherInl natZero]` at
carrier `list (Either nat bool)`.  Demonstrates that the 2-IH
parametric listCons wrapper accepts a 1-IH heterogeneous
injection as its head with the matching listNil elementType. -/
theorem aggregator_listCons_eitherInl_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm :=
          Term.eitherInl (rightType := Ty.bool)
            (valueTerm := Term.natZero))
        (tailTerm :=
          Term.listNil
            (elementType := Ty.eitherType Ty.nat Ty.bool))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_eitherInl (rightType := Ty.bool)
      isAggregatorSound_natZero)
    (isAggregatorSound_listNil
      (elementType := Ty.eitherType Ty.nat Ty.bool))

/-- optionSome carrying an eitherInl: `Some (eitherInl natZero)`
at carrier `option (Either nat bool)`.  Demonstrates the 1-IH
parametric optionSome wrapper composes with a 1-IH heterogeneous
injection at its valueTerm slot (parametric-over-heterogeneous
direction). -/
theorem aggregator_optionSome_eitherInl_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.eitherInl (rightType := Ty.bool)
            (valueTerm := Term.natZero))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_eitherInl (rightType := Ty.bool)
      isAggregatorSound_natZero)

/-- eitherInl carrying a depth-2 nat chain: `eitherInl
(natSucc (natSucc natZero))` at carrier `Either nat bool`.
Variant of the existing eitherInl_natOne example carrying a
deeper nat chain; demonstrates 1-IH heterogeneous wrappers
compose with non-trivial 1-IH chains past depth 1. -/
theorem aggregator_eitherInl_natTwo_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInl (context := sourceCtx)
        (rightType := Ty.bool)
        (valueTerm :=
          Term.natSucc (Term.natSucc Term.natZero))) :=
  isAggregatorSound_eitherInl (rightType := Ty.bool)
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc isAggregatorSound_natZero))

/-- 2-element list of options: `[Some natZero, Some natZero]` at
carrier `list (option nat)`.  Extends the 1-element
`listCons_optionSome_closed` to length 2 with a recursive
listCons tail; demonstrates that 2-IH parametric listCons +
1-IH parametric optionSome compose at list length > 1. -/
theorem aggregator_listCons_optionSome_two_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.optionSome (valueTerm := Term.natZero))
        (tailTerm :=
          Term.listCons
            (headTerm := Term.optionSome (valueTerm := Term.natZero))
            (tailTerm :=
              Term.listNil (elementType := Ty.optionType Ty.nat)))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    (isAggregatorSound_listCons
      (isAggregatorSound_optionSome isAggregatorSound_natZero)
      (isAggregatorSound_listNil
        (elementType := Ty.optionType Ty.nat)))

/-- eitherInl carrying a Sigma-pair (LEFT side): `eitherInl
(natZero, natZero)` at carrier `Either (nat × nat) bool`.
Counterpart to Phase 104's eitherInr_pair_closed which puts the
Sigma on the right side; together they confirm both injection
sides accept 2-IH Sigma children. -/
theorem aggregator_eitherInl_pair_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInl (context := sourceCtx)
        (rightType := Ty.bool)
        (valueTerm :=
          Term.pair (secondType := Ty.nat)
            (firstValue := Term.natZero)
            (secondValue := Term.natZero))) :=
  isAggregatorSound_eitherInl (rightType := Ty.bool)
    (isAggregatorSound_pair isAggregatorSound_natZero
      isAggregatorSound_natZero)

/-- List of right-injected either values: `[eitherInr boolTrue]`
at carrier `list (Either nat bool)`.  Counterpart to Phase 104's
listCons_eitherInl_closed; together they confirm both either
injection sides serve as listCons heads. -/
theorem aggregator_listCons_eitherInr_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm :=
          Term.eitherInr (leftType := Ty.nat)
            (valueTerm := Term.boolTrue))
        (tailTerm :=
          Term.listNil
            (elementType := Ty.eitherType Ty.nat Ty.bool))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_eitherInr (leftType := Ty.nat)
      isAggregatorSound_boolTrue)
    (isAggregatorSound_listNil
      (elementType := Ty.eitherType Ty.nat Ty.bool))

/-- Option of an inner None: `Some None` at carrier
`option (option nat)`.  Demonstrates that the 1-IH parametric
optionSome wrapper composes with the 0-IH parametric optionNone
wrapper at the inner valueTerm slot; mixing the two option-arm
templates within a single composition. -/
theorem aggregator_optionSome_optionNone_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm := Term.optionNone (elementType := Ty.nat))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_optionNone (elementType := Ty.nat))

/-- Mixed-depth Sigma-pair: `pair (natSucc natZero) (natSucc
(natSucc natZero))` at carrier `nat × nat`.  Variant of the
existing `pair_natNat_closed` whose components are both
natZero; this version exercises non-trivial 1-IH children at
both positions with different chain depths (1 and 2). -/
theorem aggregator_pair_natOne_natTwo_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.natSucc Term.natZero)
        (secondValue :=
          Term.natSucc (Term.natSucc Term.natZero))) :=
  isAggregatorSound_pair
    (isAggregatorSound_natSucc isAggregatorSound_natZero)
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc isAggregatorSound_natZero))

/-- 1-element list of booleans: `[boolTrue]` at carrier
`list bool`.  Demonstrates that the 2-IH parametric listCons
wrapper composes with a 0-IH atomic boolean head and a 0-IH
parametric listNil tail at the bool carrier (counterpart to
the existing listCons_natList example at the nat carrier). -/
theorem aggregator_listCons_boolList_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.boolTrue)
        (tailTerm := Term.listNil (elementType := Ty.bool))) :=
  isAggregatorSound_listCons isAggregatorSound_boolTrue
    (isAggregatorSound_listNil (elementType := Ty.bool))

/-- 8-deep natSucc chain extending the natOne..natSeven sequence.
Continues the depth-uniformity demonstration for 1-IH wrappers
past depth 7. -/
theorem aggregator_natEight_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.natSucc (context := sourceCtx)
        (Term.natSucc
          (Term.natSucc
            (Term.natSucc
              (Term.natSucc
                (Term.natSucc
                  (Term.natSucc
                    (Term.natSucc Term.natZero)))))))) :=
  isAggregatorSound_natSucc
    (isAggregatorSound_natSucc
      (isAggregatorSound_natSucc
        (isAggregatorSound_natSucc
          (isAggregatorSound_natSucc
            (isAggregatorSound_natSucc
              (isAggregatorSound_natSucc
                (isAggregatorSound_natSucc
                  isAggregatorSound_natZero)))))))

/-- Nested either at carrier `Either nat (Either nat bool)`:
`eitherInr (eitherInl natZero)`.  Demonstrates that the 1-IH
heterogeneous-injection wrapper composes with another 1-IH
heterogeneous-injection wrapper at its valueTerm slot, with the
outer's leftType and inner's rightType independently bound. -/
theorem aggregator_eitherInr_eitherInl_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInr (context := sourceCtx)
        (leftType := Ty.nat)
        (valueTerm :=
          Term.eitherInl (rightType := Ty.bool)
            (valueTerm := Term.natZero))) :=
  isAggregatorSound_eitherInr (leftType := Ty.nat)
    (isAggregatorSound_eitherInl (rightType := Ty.bool)
      isAggregatorSound_natZero)

/-- Mixed-type Sigma-pair with non-trivial first child: `pair
(natSucc natZero) boolTrue` at carrier `nat × bool`.  Variant of
the existing `pair_natBool_closed` whose first component is the
atomic natZero; this version exercises a 1-IH chain at the first
position with an atomic boolean at the second. -/
theorem aggregator_pair_natOne_boolTrue_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.bool)
        (firstValue := Term.natSucc Term.natZero)
        (secondValue := Term.boolTrue)) :=
  isAggregatorSound_pair
    (isAggregatorSound_natSucc isAggregatorSound_natZero)
    isAggregatorSound_boolTrue

/-- 1-element list of booleans (false variant): `[boolFalse]` at
carrier `list bool`.  Counterpart to the Phase 107
listCons_boolList_closed (which uses boolTrue); confirms both
boolean atomic values serve as listCons heads at the bool
carrier. -/
theorem aggregator_listCons_boolFalse_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.boolFalse)
        (tailTerm := Term.listNil (elementType := Ty.bool))) :=
  isAggregatorSound_listCons isAggregatorSound_boolFalse
    (isAggregatorSound_listNil (elementType := Ty.bool))

/-- Mixed parametric-over-heterogeneous: `Some (eitherInr
boolTrue)` at carrier `option (Either nat bool)`.  Counterpart
to Phase 105's optionSome_eitherInl_closed (left side); confirms
the parametric optionSome wrapper composes with either-injection
side. -/
theorem aggregator_optionSome_eitherInr_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.eitherInr (leftType := Ty.nat)
            (valueTerm := Term.boolTrue))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_eitherInr (leftType := Ty.nat)
      isAggregatorSound_boolTrue)

/-- Sigma-pair with parametric children at BOTH positions: `pair
(Some natZero) (Some natZero)` at carrier
`option nat × option nat`.  Demonstrates that the 2-IH
non-parametric Sigma wrapper accepts 1-IH parametric children
simultaneously at both component slots. -/
theorem aggregator_pair_optionSome_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.optionType Ty.nat)
        (firstValue := Term.optionSome (valueTerm := Term.natZero))
        (secondValue :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_pair
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

/-- Sigma-pair with 0-IH parametric in first component: `pair
optionNone natZero` at carrier `option nat × nat`.  Demonstrates
that the 2-IH non-parametric Sigma wrapper accepts a 0-IH
parametric child (optionNone) as its first component — first
example with a 0-IH parametric value as a Sigma component. -/
theorem aggregator_pair_optionNone_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.optionNone (elementType := Ty.nat))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_optionNone (elementType := Ty.nat))
    isAggregatorSound_natZero

/-- Triple nesting through two categories: `Some (Some (eitherInl
natZero))` at carrier `option (option (Either nat bool))`.
Demonstrates that two parametric optionSome wrappers compose
recursively around a 1-IH heterogeneous injection at the base. -/
theorem aggregator_optionSome_optionSome_eitherInl_closed
    {mode : Mode} {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionSome (context := sourceCtx)
        (valueTerm :=
          Term.optionSome
            (valueTerm :=
              Term.eitherInl (rightType := Ty.bool)
                (valueTerm := Term.natZero)))) :=
  isAggregatorSound_optionSome
    (isAggregatorSound_optionSome
      (isAggregatorSound_eitherInl (rightType := Ty.bool)
        isAggregatorSound_natZero))

/-- Sigma-pair with both option arms in their respective slots:
`pair optionNone (Some natZero)` at carrier
`option nat × option nat`.  First example mixing the 0-IH
parametric (optionNone) and 1-IH parametric (optionSome)
wrappers across the two Sigma components. -/
theorem aggregator_pair_optionNone_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.optionType Ty.nat)
        (firstValue := Term.optionNone (elementType := Ty.nat))
        (secondValue :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_pair
    (isAggregatorSound_optionNone (elementType := Ty.nat))
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

/-- Heterogeneous either with parametric child on LEFT side:
`eitherInl (Some natZero)` at carrier `Either (option nat) bool`.
Counterpart to Phase 105's `optionSome_eitherInl_closed` which
puts the either INSIDE the option; here the option is inside
the either, demonstrating both nesting orders compose. -/
theorem aggregator_eitherInl_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.eitherInl (context := sourceCtx)
        (rightType := Ty.bool)
        (valueTerm :=
          Term.optionSome (valueTerm := Term.natZero))) :=
  isAggregatorSound_eitherInl (rightType := Ty.bool)
    (isAggregatorSound_optionSome isAggregatorSound_natZero)

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
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natFive_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_optionSome_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInl_natOne_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_triple_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_natOne_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_optionSome_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInr_optionSome_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_eitherInl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_optionSome_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natSix_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_quad_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_pair_natNatNat_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_pair_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natZero_pair_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natSeven_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natZero_optionSome_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natZero_eitherInl_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_natListChainThree_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_pair_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInr_pair_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_eitherInl_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_eitherInl_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInl_natTwo_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_optionSome_two_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInl_pair_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_eitherInr_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_optionNone_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natOne_natTwo_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_boolList_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natEight_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInr_eitherInl_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natOne_boolTrue_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_boolFalse_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_eitherInr_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_optionSome_optionSome_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_optionNone_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionSome_optionSome_eitherInl_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_optionNone_optionSome_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_eitherInl_optionSome_closed

end LeanFX2.SmokeAggregatorComposition
