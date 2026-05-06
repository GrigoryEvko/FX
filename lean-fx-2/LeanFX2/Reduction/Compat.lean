import LeanFX2.Reduction.RawParCompatible

/-! # Reduction/Compat — rename + subst compatibility

Renaming and substitution preserve every reduction relation:
* `Step` (single step)
* `Step.par` (parallel reduction)
* `StepStar` (multi-step) — via `mapStep`
* `Conv` (definitional conversion) — via `mapStep`

## The big simplification (from lean-fx)

In lean-fx, β-arms required a separate `RawConsistent` hypothesis
threaded through ~17 files because `Term.subst0_term` consulted the
raw side via a `forRaw` field that could be inconsistent with the
typed `forTy`.  In lean-fx-2, `RawTerm scope` is a Term type-level
index — every typed Term is automatically raw-consistent — so no
threading is needed.  Subst-compat proofs are ~30% smaller.

## Shipped slice

This module currently carries the raw-layer compatibility API that the typed
bridge and confluence layers consume.  It deliberately stays in Layer 2 and
therefore does not import the later `LeanFX2.Bridge` module.

The still-missing typed endpoint theorem

```lean
Step.par (source.rename rho) (target.rename rho)
```

has to thread the dependent casts produced by `Term.rename` / `Term.subst`
through every beta and eliminator arm.  That remains a separate Day-2
obligation; the declarations below are honest raw-level compatibility names
over the already-proved raw induction theorems.

## Remaining phase plan

* Step 1 (cong-only Step.rename_compatible) — port all ~30 cong
  cases first, keeping β/ι behind helper lemmas.
* Step 2 (Term.rename_subst0_HEq) — the subst-rename commute lemma
  at the typed-Term level, needed for β cases.
* Step 3 (β/ι cases of Step.rename_compatible).
* Step 4 (Step.subst_compatible) — mirror via TermSubst.
* Step 5 (Step.par.rename_compatible / subst_compatible).
* Step 6 (StepStar / Conv corollaries via mapStep).
-/

namespace LeanFX2

namespace RawStep

namespace par

/-- Compatibility name for raw parallel reduction under renaming.

This is a thin, audited API wrapper around `RawStep.par.rename`; keeping it in
`Reduction/Compat.lean` gives downstream code a stable import that names the
compatibility obligation directly. -/
theorem rename_compatible {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.rename rawRenaming)
                (afterTerm.rename rawRenaming) :=
  RawStep.par.rename rawRenaming parallelStep

/-- Compatibility name for raw parallel reduction under two pointwise-related
substitutions.

This is the general joint-substitution theorem already proved by induction in
`RawParCompatible.lean`, re-exported here under the Day-2 compatibility API. -/
theorem subst_compatible {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst firstSubst)
                (afterTerm.subst secondSubst) :=
  RawStep.par.subst_par substsRelated parallelStep

/-- Same-substitution corollary of `subst_compatible`. -/
theorem subst_compatible_same {sourceScope targetScope : Nat}
    (rawSubst : RawTermSubst sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst rawSubst)
                (afterTerm.subst rawSubst) :=
  RawStep.par.subst_compatible
    (fun position => RawStep.par.refl (rawSubst position))
    parallelStep

end par

end RawStep

end LeanFX2
