import LeanFX2.Term
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Reducibility.Basic — strong-normalization foundation

This module hosts the strong-normalization primitives that the
Tait reducibility candidate machinery builds on:

* `RawStep.parProgress` — non-reflexive parallel-progress reduction
  (a `RawStep.par` step that actually fires at least one redex,
  distinguishing source from target so the trivial `RawStep.par.refl`
  loop is excluded).
* `RawTerm.isStronglyNormalizing` — inductive Prop closure under
  non-trivial parallel reduction.  Same shape as Lean's `Acc` but
  ships its own recursor, so we avoid the kernel's Acc-dependency
  budget.
* `Term.isStronglyNormalizing` — typed SN as raw SN of the term's
  raw projection.

The module is the first slice carved out of the historical 21k-line
`Reducibility.lean`; the predicates here are deliberately
`Reducible`-independent so that downstream sub-modules
(`Reducibility/Neutral.lean`, `Reducibility.lean` proper) can
import them without forming a cycle.

## Root status

Layer 3 metatheory leaf.  Stable across the K12 SN cascade. -/

namespace LeanFX2

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

end LeanFX2
