import LeanFX2.Foundation.PolyCell.Core.StepStarConfluence
import LeanFX2.Foundation.PolyCell.Core.StepSubst
import LeanFX2.Foundation.PolyCell.Core.StepRename
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0

/-! # Foundation/PolyCell/Core/ConvSubstRename
   — Conv preservation under substitution + renaming + β-redex shape

M-Conv-subst-rename (#370, 2026-05-28).  Ships the Conv-level
preservation theorems that the 5-agent gap audit (Agent 2) surfaced
as missing.  Currently `Step.subst` / `StepStar.subst` ship at
`StepSubst.lean:21,184` and `Step.rename` / `StepStar.rename` ship at
`StepRename.lean:156` (via M-substrate-1 #365), but the Conv-layer
wrappers do not exist as named theorems — so downstream typed-layer
SR (M46 #295) + typed weakening (M47 #296) have no clean substrate
to cite.

## API surface

* `Conv.subst : ∀ σ, Conv a b → Conv (subst σ a) (subst σ b)`
* `Conv.rename : ∀ ρ, Conv a b → Conv (rename ρ a) (rename ρ b)`
* `Conv.weaken : Conv a b → Conv (rename weaken a) (rename weaken b)`
  — common single-binder-shift specialization.
* `Conv.subst0 : Conv body_L body_R → Conv arg_L arg_R →
                 Conv (subst0 body_L arg_L) (subst0 body_R arg_R)`
  — congruence at β-redex shape (two-arg form).

Plus the bridging helper:
* `RawTermSubst.singleton_pointwise_stepStar` — promotes a StepStar
  on the arg to a PointwiseStepStar on the singleton substitutions.

## Proof technique

`Conv.subst` and `Conv.rename` are 3-line extract-Join + apply-on-
each-leg proofs citing the shipped `StepStar.subst` and
`StepStar.rename` respectively.

`Conv.subst0` is the only non-trivial proof.  The challenge: the
substitution itself DEPENDS on the arg, so plain `Conv.subst` doesn't
suffice — we need a pointwise property bridging two substitutions
that differ in the arg position.

Two-step composition per leg:
1. **Body step**: `subst (singleton arg_X) body_X →* subst (singleton
   arg_X) body_common` via `StepStar.subst` on `bodyChain` (body
   reduces, substitution fixed).
2. **Arg step**: `subst (singleton arg_X) body_common →* subst
   (singleton arg_common) body_common` via
   `RawTerm.subst_pointwise_stepStar` (StepSubst.lean:1230)
   applied to the singleton's pointwise lift.

Both steps compose via `StepStar.trans_compose` to land at the
common reduct `subst0 body_common arg_common`.

## Why pointwise needed

The singleton substitution maps:
* position 0 → arg
* position k+1 → var k

When the arg reduces, only position 0 of the singleton changes; the
higher positions are reflexive.  This is exactly the shape of
`PointwiseStepStar` defined at `StepSubst.lean:1096-1100`.  The new
helper `RawTermSubst.singleton_pointwise_stepStar` packages this
observation: given `StepStar arg_left arg_right`, construct
`PointwiseStepStar (singleton arg_left) (singleton arg_right)` by
direct Fin position-zero / position-succ case analysis.

## Substrate consumed

* `Conv` definition + `Conv.refl` from `StepStarConfluence.lean:18-176`.
* `StepStar.subst` from `StepSubst.lean:184`.
* `StepStar.rename` from `StepRename.lean:156` (via M-substrate-1).
* `StepStar.trans_compose` from `StepStar.lean:210`.
* `RawTermSubst.PointwiseStepStar` + `subst_pointwise_stepStar` from
  `StepSubst.lean:1096,1230`.
* `RawTermSubst.singleton` (@[reducible]) from `RawTermSubst0.lean:102`.
* `RawTerm.subst0` (@[reducible]) from `RawTermSubst0.lean:118`.

## Zero-axiom verification

All 5 declarations close by direct construction + Fin-position
struct match.  No `induction` (only `obtain` destructuring of
existential Conv proofs).  No `simp`, no `omega`, no propext.
The Fin case-analysis uses direct `⟨0, _⟩` / `⟨_ + 1, _⟩` struct
matching per `feedback_lean_fin_cases_axiom` recipe — axiom-free.

Audit-gated.  Consumers: M46 #295 ★ Typed SR, M47 #296 typed
weakening + substitution, M-Conv-equivalence #371 (composes with
refl/symm/trans for the Equivalence instance), M55a #364 typed
β+η Decidable Conv. -/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Pointwise StepStar lift to singleton substitutions.**

If `leftArg` reduces by `StepStar` to `rightArg`, then the singleton
substitutions `singleton leftArg` and `singleton rightArg` are
pointwise `StepStar`-related:
* Position 0: maps via the arg chain itself.
* Position k+1: reflexive (both produce `var k`, scope-invariant).

This is the bridging helper that lets `Conv.subst0` traverse the
arg side of a β-redex's substitution. -/
theorem RawTermSubst.singleton_pointwise_stepStar {scope : Nat}
    {leftArg rightArg : RawTerm scope}
    (argChain : StepStar leftArg rightArg) :
    RawTermSubst.PointwiseStepStar
      (RawTermSubst.singleton leftArg)
      (RawTermSubst.singleton rightArg) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact argChain
  | ⟨_ + 1, _⟩ => exact StepStar.refl _

/-- **Conv preserved by substitution.** Extract the Join from the
input Conv, apply `StepStar.subst` to both legs, repackage as
Conv. -/
theorem Conv.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {leftTerm rightTerm : RawTerm sourceScope}
    (convProof : Conv leftTerm rightTerm) :
    Conv (RawTerm.subst substitution leftTerm)
         (RawTerm.subst substitution rightTerm) := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convProof
  exact ⟨RawTerm.subst substitution commonReduct,
         StepStar.subst substitution leftChain,
         StepStar.subst substitution rightChain⟩

/-- **Conv preserved by renaming.** Sibling to `Conv.subst` via
`StepStar.rename` (M-substrate-1 #365). -/
theorem Conv.rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {leftTerm rightTerm : RawTerm sourceScope}
    (convProof : Conv leftTerm rightTerm) :
    Conv (RawTerm.rename rawRenaming leftTerm)
         (RawTerm.rename rawRenaming rightTerm) := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convProof
  exact ⟨RawTerm.rename rawRenaming commonReduct,
         StepStar.rename rawRenaming leftChain,
         StepStar.rename rawRenaming rightChain⟩

/-- **Conv preserved by single-binder weakening.** Specialization of
`Conv.rename` to `RawRenaming.weaken` — the common case when
traversing under a single lambda binder.  Used by typed weakening
(M47 #296) to lift Conv across context extensions. -/
theorem Conv.weaken {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (convProof : Conv leftTerm rightTerm) :
    Conv (RawTerm.rename RawRenaming.weaken leftTerm)
         (RawTerm.rename RawRenaming.weaken rightTerm) :=
  Conv.rename RawRenaming.weaken convProof

/-- **Conv preserved by single-position substitution at β-redex
shape.** Two-arg form: if body and arg are independently Conv, then
their subst0 results are Conv.

This is the load-bearing congruence rule for β-redex reasoning:
when the SR proof reduces `(lam body) arg` to `subst0 body arg`,
the resulting Conv must respect both body-Conv and arg-Conv at
once.

Proof structure (per leg):
* Body step: `StepStar.subst (singleton arg_X) bodyChain` reduces
  the body's side of the substitution while fixing the arg.
* Arg step: `subst_pointwise_stepStar (singleton_pointwise_stepStar
  argChain) bodyCommon` reduces the arg's side via the singleton's
  pointwise lift while fixing the body.
* `StepStar.trans_compose` chains them to land at the common
  reduct `subst0 bodyCommon argCommon`.

Both legs land at the same common reduct, so the Join packages
cleanly. -/
theorem Conv.subst0 {scope : Nat}
    {bodyLeft bodyRight : RawTerm (scope + 1)}
    {argLeft argRight : RawTerm scope}
    (bodyConv : Conv bodyLeft bodyRight)
    (argConv : Conv argLeft argRight) :
    Conv (RawTerm.subst0 bodyLeft argLeft)
         (RawTerm.subst0 bodyRight argRight) := by
  obtain ⟨bodyCommon, bodyLeftChain, bodyRightChain⟩ := bodyConv
  obtain ⟨argCommon, argLeftChain, argRightChain⟩ := argConv
  refine ⟨RawTerm.subst0 bodyCommon argCommon, ?_, ?_⟩
  · -- left leg: subst0 bodyLeft argLeft →* subst0 bodyCommon argCommon
    exact StepStar.trans_compose
      (StepStar.subst (RawTermSubst.singleton argLeft) bodyLeftChain)
      (RawTerm.subst_pointwise_stepStar
        (RawTermSubst.singleton_pointwise_stepStar argLeftChain)
        bodyCommon)
  · -- right leg: subst0 bodyRight argRight →* subst0 bodyCommon argCommon
    exact StepStar.trans_compose
      (StepStar.subst (RawTermSubst.singleton argRight) bodyRightChain)
      (RawTerm.subst_pointwise_stepStar
        (RawTermSubst.singleton_pointwise_stepStar argRightChain)
        bodyCommon)

end LeanFX2.Foundation.PolyCell.Core
