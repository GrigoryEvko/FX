import LeanFX2.Term
import LeanFX2.Reduction.RawPar

/-! # LeanFX2.Reducibility — Tait reducibility candidates (K12.1+K12.2)

K12.1 introduces the Tait/Girard reducibility-candidate predicate
`Reducible` at the foundation of strong normalization (SN).
K12.2 ships the first per-Ty arm: `Reducible.nat` for closed
naturals.

## Strong normalization via inductive Prop closure

`RawStep.par` is reflexive (`RawStep.par.refl` always inhabits
`RawStep.par raw raw`).  An Acc-based SN encoding over `par`
would therefore be trivially false — `raw → raw → ...` is an
infinite trace under reflexivity alone.

`Acc` / `WellFounded` are also explicitly banned in the kernel
tier (`GatesCore.lean:51` budget 0) to keep recursion
structural.  We instead define SN directly as an inductive
Prop whose constructor closes over non-reflexive parallel
reductions:

```
RawStep.parProgress src tgt := RawStep.par src tgt ∧ src ≠ tgt
inductive RawTerm.isStronglyNormalizing : RawTerm scope → Prop
  | intro (raw) :
      (∀ target, parProgress raw target →
        RawTerm.isStronglyNormalizing target) →
      RawTerm.isStronglyNormalizing raw
```

This is the same shape as Lean's `Acc` but emits its own
recursor `RawTerm.isStronglyNormalizing.rec` and incurs no Acc
dependency.  Semantically: `raw` is SN iff every non-trivial
parallel reduction from `raw` leads to a target that is itself
SN — the smallest fixed point under the reduction closure.

`Term.isStronglyNormalizing term := RawTerm.isStronglyNormalizing
term.toRaw` — typed SN reduces to raw SN of the term's raw
projection (lifts through `Term.toRaw` definitionally).

## The Reducible predicate (Tait 1967 / Girard 1972)

Tait/Girard define reducibility by induction on type structure:
RC at a base type is SN, RC at a function type is "maps RC to
RC", RC at a Pi is "maps RC under substitution to RC", and so
on.  The structure is uniform but each Ty constructor
specializes the closure.

K12.1 ships the inductive skeleton; K12.2 fills the first arm.
Future arms K12.3-K12.16 extend `Reducible` to the remaining Ty
constructors.  The final SN headline (`theorem
strong_normalization : HasType ... → SN t`, task K12.27 / M04
#1273) requires the fundamental lemma threading reducibility
through typing derivations (K12.18-K12.26).

## What ships now

* `RawStep.parProgress` — non-reflexive parallel reduction
  predicate (def, not inductive — just `par ∧ ≠`).
* `RawTerm.isStronglyNormalizing` — inductive Prop closure under
  parProgress.
* `Term.isStronglyNormalizing` — typed SN via raw SN of toRaw.
* `Reducible` — inductive Prop indexed by target type.
* `Reducible.nat` — closed-natural reducibility = SN.

## Root status

Layer 3 metatheory (top-level `LeanFX2.Reducibility` module —
outside the `Term/` and `Reduction/` layer-contract namespaces,
since the predicate spans both Term and RawPar imports).
Provides foundation for the Tait SN theorem (M04 / K12.27).

Pairs with K11.x polygraph layer (orthogonal axes: polygraph
encodes reduction coherences as cells; reducibility encodes
termination as a Prop fixed point).

## Task anchor

K12.1 + K12.2 in extended-roadmap.md.  Pairs with K12.3–K12.30
filling remaining Ty arms + the fundamental-lemma cascade.
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
Equivalent to `Acc (inverse parProgress) raw` but emits its own
recursor — does not depend on Lean's `Acc` machinery, satisfying
the kernel-tier no-Acc discipline. -/
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

/-- The Tait reducibility-candidate predicate, indexed by target
type.  Per-Ty arms ship incrementally across K12.x.

K12.2 ships `Reducible.nat`: a closed natural-typed term is
reducible iff it is strongly normalizing.  Matches Tait's
base-type clause — at non-function types, reducibility reduces
to plain SN because there is no sub-structure to recurse into. -/
inductive Reducible : ∀ {mode : Mode} {level scope : Nat}
                        {context : Ctx mode level scope}
                        (typeIndex : Ty level scope)
                        {raw : RawTerm scope},
                      Term context typeIndex raw → Prop
  /-- K12.2: a closed natural-typed term is reducible iff it is
  strongly normalizing.  Base-type clause — no function
  structure forces recursion into reducibility at sub-types. -/
  | nat {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {natRaw : RawTerm scope}
      (natTerm : Term context Ty.nat natRaw) :
      Term.isStronglyNormalizing natTerm →
      Reducible Ty.nat natTerm

end LeanFX2
