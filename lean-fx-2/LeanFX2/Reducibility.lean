import LeanFX2.Term
import LeanFX2.Reduction.RawPar

/-! # LeanFX2.Reducibility — Tait reducibility candidates

K12.1-K12.5 pivot: `Reducible` is a `def`-by-recursion on Ty
covering all 25 Ty constructors.  The pivot resolves the
strict-positivity wall that blocked the K12.5 inductive arrow
clause — `Reducible` recursive references descend on Ty's
sub-components via Lean's structural recursion via `Ty.rec`
(no Acc dependency, no propext leak under full enum).

## Architectural history

K12.1+K12.2 originally shipped `Reducible` as an `inductive Prop`
with a `Reducible.nat` SN closure arm.  K12.3+K12.4 added five
more closed-leaf arms (bool / unit / empty / interval / universe)
identical in shape.

K12.5 (this commit) attempted to extend the inductive with the
standard Tait function-type closure:

```
| arrow ... (closesUnderApp :
      ∀ arg, Reducible domainType arg →
             Reducible codomainType (Term.app term arg)) :
    Reducible (Ty.arrow A B) term
```

Lean 4 v4.29.1 rejected with:

```
(kernel) arg #9 of 'LeanFX2.Reducible.arrow' has a
non positive occurrence of the datatypes being declared
```

The closure's hypothesis `Reducible domainType arg` sits LEFT
of an arrow inside the constructor argument — a non-positive
occurrence the kernel rejects.  Canonical mathlib pattern:
pivot from `inductive` to `def`-by-recursion on Ty.  This works
because recursive references descend on a structurally-smaller
Ty (`domainType` and `codomainType` are proper sub-terms of
`Ty.arrow domainType codomainType`).

## The Reducible predicate (Tait 1967 / Girard 1972)

Tait/Girard define reducibility by induction on type structure:
RC at a base type is SN, RC at a function type is "maps RC to
RC", etc.  Each Ty constructor specializes the closure.

This file ships:

* `RawStep.parProgress` — non-reflexive parallel reduction
  (par AND source ≠ target).  Sidesteps the `RawStep.par.refl`
  trivial loop in the SN encoding.
* `RawTerm.isStronglyNormalizing` — inductive Prop closure
  under non-trivial parallel reduction.  Same shape as Lean's
  `Acc` but emits its own recursor, no Acc dependency
  (satisfies `GatesCore.acc_dependent_budget` 0).
* `Term.isStronglyNormalizing` — typed SN as raw SN of the
  term's raw projection.
* `Reducible` — def-by-recursion on Ty with one arm per
  constructor (25 total).  Closed leaves use SN (Tait's
  base-type clause); arrow uses the corrected Wood/Atkey 2022
  closure under application bundled with SN.

## Arm-by-arm semantics

* **Closed leaves** (unit / bool / nat / empty / interval /
  universe / tyVar): `Term.isStronglyNormalizing term`.
  Matches Tait's base-type clause — no function structure
  forces recursion into sub-types.
* **arrow A B** (K12.5): `SN(term) ∧ ∀ arg, Reducible A arg →
  Reducible B (Term.app term arg)`.  Bundles SN with the
  closure for use by the fundamental lemma.
* **piTy A B** (K12.6, weak closure): `SN(term) ∧ ∀ arg,
  Reducible A arg → SN(Term.appPi term arg)`.  The full Tait
  clause `Reducible (B.subst0 A arg) (Term.appPi term arg)`
  fails structural recursion (substituted codomain is not a
  strict sub-term), so K12.6 ships the weak variant.  Stronger
  than SN-fallback (preserves SN under reducible application);
  weaker than the full Tait clause (no Reducible at the
  substituted codomain).  Full closure reserved for a future
  Kripke logical relation refactor.
* **sigmaTy A B** (K12.7, asymmetric closure): `SN(term) ∧
  Reducible A (Term.fst term) ∧ SN(Term.snd term)`.  Asymmetric
  because `firstType` IS a strict sub-term of `Ty.sigmaTy
  firstType secondType` (so full Reducible recurses), but the
  snd projection's type is `secondType.subst0 firstType ...`
  (substituted, same wall as K12.6 piTy codomain).  Full
  Reducible-snd closure reserved for the Kripke refactor.
* **All remaining constructors** (~15 type formers: id,
  listType, optionType, eitherType, path, glue, oeq,
  idStrict, equiv, refine, record, codata, session, effect,
  modal): SN-fallback (admissible but weak — every reducible
  term is at least SN).  K12.8-K12.16 tighten each to its
  type-former-specific closure.

The pivot keeps K12.2-K12.4's six closed-leaf arms semantically
correct (SN IS the proper Tait clause for closed-leaf types).
K12.5 adds the proper arrow closure.  K12.6+ refines the
remaining ~17 weak-SN arms incrementally.

## Wood/Atkey 2022 corrected Lam rule

Standard Tait reducibility (Tait 1967) uses the arrow closure
`∀ a, RC(A, a) → RC(B, f a)`.  Atkey 2018's original graded
Lam rule was unsound; Wood/Atkey 2022 corrected it via context
division (§6.2 of fx_design.md).  At the reducibility layer,
the closure formula is unchanged; the correction lives in the
Lam typing rule itself (`Term.lam`), not in `Reducible`.

## What ships

* `RawStep.parProgress` (def, K12.1)
* `RawTerm.isStronglyNormalizing` (inductive Prop, K12.1)
* `Term.isStronglyNormalizing` (def, K12.1)
* `Reducible` (def by recursion on 25 Ty ctors, K12.1-K12.5)

## Root status

Layer 3 metatheory (top-level `LeanFX2.Reducibility` module).
Provides foundation for the Tait SN theorem (M04 / K12.27).
K12.6-K12.16 tighten remaining weak-SN arms.  K12.18-K12.26
ship the fundamental lemma threading Reducible through Term
typing derivations.

## Task anchors

K12.1 (#1758), K12.2 (#1759), K12.3 (#1760), K12.4 (#1761),
K12.5 (#1762) in the FX task tracker.  Pairs with K12.6-K12.30
filling remaining Ty arm closures + fundamental-lemma cascade.
-/

namespace LeanFX2

/-- Non-reflexive parallel-progress reduction: a `RawStep.par`
step that fires at least one redex (source and target distinct).
Distinguishing source from target sidesteps the `RawStep.par.refl`
trivial loop. -/
def RawStep.parProgress {scope : Nat} (source target : RawTerm scope) : Prop :=
  RawStep.par source target ∧ source ≠ target

/-- Strong normalization of a raw term: inductively-defined
closure under non-trivial parallel reduction.

`isStronglyNormalizing raw` holds iff every parallel-progress
reduction `raw → target` leads to a target that is itself SN.
Equivalent to `Acc (inverse parProgress) raw` but emits its
own recursor — no Acc dependency, satisfies the kernel-tier
no-Acc discipline. -/
inductive RawTerm.isStronglyNormalizing : ∀ {scope : Nat},
    RawTerm scope → Prop
  /-- Constructor closes SN over the non-trivial reduction
  successors.  Smallest fixed point — inhabits exactly the
  well-founded part of inverse `parProgress`. -/
  | intro {scope : Nat} (raw : RawTerm scope)
      (closure : ∀ (target : RawTerm scope),
                   RawStep.parProgress raw target →
                   RawTerm.isStronglyNormalizing target) :
      RawTerm.isStronglyNormalizing raw

/-- Strong normalization of a typed term: SN of its raw
projection.  Lifts through `Term.toRaw` definitionally (the
typed `Term` carries the raw form as a structural index). -/
def Term.isStronglyNormalizing {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (_term : Term context sourceType sourceRaw) : Prop :=
  RawTerm.isStronglyNormalizing sourceRaw

/-- The Tait reducibility-candidate predicate, defined by
structural recursion on Ty.

Closed-leaf arms (unit / bool / nat / empty / interval /
universe / tyVar) use plain SN per Tait's base-type clause.
The arrow arm bundles SN with the closure under application
per Wood/Atkey 2022's corrected Lam rule.  Remaining arms
(piTy / sigmaTy / id / list / option / either / path / glue /
oeq / idStrict / equiv / refine / record / codata / session /
effect / modal) ship the SN-fallback closure; K12.6-K12.16
tighten each to its type-former-specific shape. -/
def Reducible {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  -- Closed leaves (K12.2-K12.4): SN base-type clause
  | Ty.unit, _, term => Term.isStronglyNormalizing term
  | Ty.bool, _, term => Term.isStronglyNormalizing term
  | Ty.nat, _, term => Term.isStronglyNormalizing term
  | Ty.empty, _, term => Term.isStronglyNormalizing term
  | Ty.interval, _, term => Term.isStronglyNormalizing term
  | Ty.universe _ _, _, term => Term.isStronglyNormalizing term
  | Ty.tyVar _, _, term => Term.isStronglyNormalizing term
  -- Function type (K12.5): SN + closure under application
  | Ty.arrow domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Reducible codomainType (Term.app functionTerm argumentTerm)
  -- Dependent Π type (K12.6, weak closure): SN + SN-after-app.
  -- The full Tait dep-Π closure (`Reducible (B.subst0 A arg)
  -- (Term.appPi f arg)`) recurses on the substituted codomain
  -- `B.subst0 domainType argumentRaw` — NOT a structural
  -- sub-term of `Ty.piTy A B`, so the structural-recursion
  -- checker rejects it (probed 2026-05-11: "Please use
  -- `termination_by` to specify a decreasing measure",
  -- requires WellFounded.fix → Acc, banned by GatesCore
  -- line 51).  The weak closure recurses only on `domainType`
  -- (strict sub-term) and demands SN of the result.  Stronger
  -- than pure SN-fallback (the function preserves SN under
  -- reducible argument application) but weaker than the full
  -- Tait clause.  The full closure ships in a future Kripke
  -- logical relation refactor (reserve K12.6.full for that).
  | Ty.piTy domainType _, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm)
  -- Dependent Σ type (K12.7, asymmetric closure): SN + full
  -- Reducible on fst projection (firstType IS a strict sub-term
  -- of `Ty.sigmaTy firstType secondType`, so structural recursion
  -- works) + weak SN on snd projection (its type is
  -- `secondType.subst0 firstType (RawTerm.fst pairRaw)` — same
  -- substituted-sub-term wall as K12.6's piTy codomain).  Full
  -- Reducible-snd closure ships in the future Kripke logical
  -- relation refactor.
  | Ty.sigmaTy firstType _, _, pairTerm =>
      Term.isStronglyNormalizing pairTerm ∧
      Reducible firstType (Term.fst pairTerm) ∧
      Term.isStronglyNormalizing (Term.snd pairTerm)
  -- Remaining type formers (K12.8-K12.16 TODO): SN-fallback
  | Ty.id _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.listType _, _, term => Term.isStronglyNormalizing term
  | Ty.optionType _, _, term => Term.isStronglyNormalizing term
  | Ty.eitherType _ _, _, term => Term.isStronglyNormalizing term
  | Ty.path _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.glue _ _, _, term => Term.isStronglyNormalizing term
  | Ty.oeq _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.idStrict _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.equiv _ _, _, term => Term.isStronglyNormalizing term
  | Ty.refine _ _, _, term => Term.isStronglyNormalizing term
  | Ty.record _, _, term => Term.isStronglyNormalizing term
  | Ty.codata _ _, _, term => Term.isStronglyNormalizing term
  | Ty.session _, _, term => Term.isStronglyNormalizing term
  | Ty.effect _ _, _, term => Term.isStronglyNormalizing term
  | Ty.modal _ _, _, term => Term.isStronglyNormalizing term

end LeanFX2
