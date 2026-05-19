import Lean
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.StepStar

/-! # Tools/Tactics/Cast — cast helpers for Step / Step.par

`Step.castBoth`, `Step.castSource`, `Step.castTarget`, and
`Step.par.cast{Both,Source,Target}` thread Eq through Step inhabitants
when types align via Eq.  These show up frequently in subst β-arms.

## Helpers

```lean
def Step.castBoth (typeEq : ty1 = ty2) (sourceEq : raw1 = raw1')
    (targetEq : raw2 = raw2')
    (s : Step (ctx := ctx) (ty := ty1) src tgt) :
    Step (ctx := ctx) (ty := ty2) ... := ...

def Step.castSource (sourceEq : raw1 = raw1')
    (s : Step (ctx := ctx) (ty := ty) src tgt) :
    Step (ctx := ctx) (ty := ty) ... := ...

def Step.castTarget (targetEq : raw2 = raw2')
    (s : Step (ctx := ctx) (ty := ty) src tgt) :
    Step (ctx := ctx) (ty := ty) ... := ...
```

Plus parallel `Step.par.cast*` variants.

## Why cast helpers

In β-rule's RHS (e.g., `Term.subst0 body arg`), the resulting type
sometimes needs cast through `Ty.weaken_subst_singleton` or similar.
Threading these casts through Step inhabitants keeps the proofs
clean.

## In lean-fx-2

Casts are needed less than in lean-fx because:
* Subst is unified — no `subst0` vs `subst0_term` distinction
* β-rule RHS uses `Term.subst0` directly with raw indices propagating
* Only the `Ty.weaken_subst_singleton` cast remains (intrinsic to
  the algebra)

## Dependencies

* `Reduction/Step.lean`, `Reduction/ParRed.lean`

## Downstream

* `Reduction/Compat.lean`
* `Confluence/CdLemma.lean`

## Implementation plan (Layer 12)

1. Define `Step.cast*` and `Step.par.cast*` helpers
2. Smoke: round-trip cast (cast + reverse-cast = identity)

Target: ~200 lines.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Step cast transport -/

syntax "fx_step_cast_source_type " term " using " term : tactic
syntax "fx_step_cast_target_type " term " using " term : tactic
syntax "fx_step_cast_source_raw " term " using " term : tactic
syntax "fx_step_cast_target_raw " term " using " term : tactic
syntax "fx_step_cast_source_term " term " using " term : tactic
syntax "fx_step_cast_target_term " term " using " term : tactic

syntax "fx_step_cast_source_type_symm " term " using " term : tactic
syntax "fx_step_cast_target_type_symm " term " using " term : tactic
syntax "fx_step_cast_source_raw_symm " term " using " term : tactic
syntax "fx_step_cast_target_raw_symm " term " using " term : tactic
syntax "fx_step_cast_source_term_symm " term " using " term : tactic
syntax "fx_step_cast_target_term_symm " term " using " term : tactic

macro_rules
  | `(tactic| fx_step_cast_source_type $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceType $castEquality $singleStep)
  | `(tactic| fx_step_cast_target_type $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetType $castEquality $singleStep)
  | `(tactic| fx_step_cast_source_raw $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceRaw $castEquality $singleStep)
  | `(tactic| fx_step_cast_target_raw $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetRaw $castEquality $singleStep)
  | `(tactic| fx_step_cast_source_term $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceTerm $castEquality $singleStep)
  | `(tactic| fx_step_cast_target_term $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetTerm $castEquality $singleStep)
  | `(tactic| fx_step_cast_source_type_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceType ($castEquality).symm $singleStep)
  | `(tactic| fx_step_cast_target_type_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetType ($castEquality).symm $singleStep)
  | `(tactic| fx_step_cast_source_raw_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceRaw ($castEquality).symm $singleStep)
  | `(tactic| fx_step_cast_target_raw_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetRaw ($castEquality).symm $singleStep)
  | `(tactic| fx_step_cast_source_term_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castSourceTerm ($castEquality).symm $singleStep)
  | `(tactic| fx_step_cast_target_term_symm $castEquality using $singleStep) =>
      `(tactic| exact LeanFX2.Step.castTargetTerm ($castEquality).symm $singleStep)

macro "fx_step_cast_using " singleStep:term : tactic =>
  `(tactic|
    first
      | exact LeanFX2.Step.castSourceType _ $singleStep
      | exact LeanFX2.Step.castTargetType _ $singleStep
      | exact LeanFX2.Step.castSourceRaw _ $singleStep
      | exact LeanFX2.Step.castTargetRaw _ $singleStep
      | exact LeanFX2.Step.castSourceTerm _ $singleStep
      | exact LeanFX2.Step.castTargetTerm _ $singleStep)

/-! ## Step.par cast transport -/

syntax "fx_par_cast_source_type " term " using " term : tactic
syntax "fx_par_cast_target_type " term " using " term : tactic
syntax "fx_par_cast_source_raw " term " using " term : tactic
syntax "fx_par_cast_target_raw " term " using " term : tactic
syntax "fx_par_cast_source_term " term " using " term : tactic
syntax "fx_par_cast_target_term " term " using " term : tactic

syntax "fx_par_cast_source_type_symm " term " using " term : tactic
syntax "fx_par_cast_target_type_symm " term " using " term : tactic
syntax "fx_par_cast_source_raw_symm " term " using " term : tactic
syntax "fx_par_cast_target_raw_symm " term " using " term : tactic
syntax "fx_par_cast_source_term_symm " term " using " term : tactic
syntax "fx_par_cast_target_term_symm " term " using " term : tactic

macro_rules
  | `(tactic| fx_par_cast_source_type $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceType $castEquality $parallelStep)
  | `(tactic| fx_par_cast_target_type $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetType $castEquality $parallelStep)
  | `(tactic| fx_par_cast_source_raw $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceRaw $castEquality $parallelStep)
  | `(tactic| fx_par_cast_target_raw $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetRaw $castEquality $parallelStep)
  | `(tactic| fx_par_cast_source_term $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceTerm $castEquality $parallelStep)
  | `(tactic| fx_par_cast_target_term $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetTerm $castEquality $parallelStep)
  | `(tactic| fx_par_cast_source_type_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceType ($castEquality).symm $parallelStep)
  | `(tactic| fx_par_cast_target_type_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetType ($castEquality).symm $parallelStep)
  | `(tactic| fx_par_cast_source_raw_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceRaw ($castEquality).symm $parallelStep)
  | `(tactic| fx_par_cast_target_raw_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetRaw ($castEquality).symm $parallelStep)
  | `(tactic| fx_par_cast_source_term_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castSourceTerm ($castEquality).symm $parallelStep)
  | `(tactic| fx_par_cast_target_term_symm $castEquality using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.castTargetTerm ($castEquality).symm $parallelStep)

macro "fx_par_cast_using " parallelStep:term : tactic =>
  `(tactic|
    first
      | exact LeanFX2.Step.par.castSourceType _ $parallelStep
      | exact LeanFX2.Step.par.castTargetType _ $parallelStep
      | exact LeanFX2.Step.par.castSourceRaw _ $parallelStep
      | exact LeanFX2.Step.par.castTargetRaw _ $parallelStep
      | exact LeanFX2.Step.par.castSourceTerm _ $parallelStep
      | exact LeanFX2.Step.par.castTargetTerm _ $parallelStep)

/-! ## StepStar cast transport -/

syntax "fx_stepstar_cast_source_type " term " using " term : tactic
syntax "fx_stepstar_cast_target_type " term " using " term : tactic
syntax "fx_stepstar_cast_source_term " term " using " term : tactic
syntax "fx_stepstar_cast_target_term " term " using " term : tactic

syntax "fx_stepstar_cast_source_type_symm " term " using " term : tactic
syntax "fx_stepstar_cast_target_type_symm " term " using " term : tactic
syntax "fx_stepstar_cast_source_term_symm " term " using " term : tactic
syntax "fx_stepstar_cast_target_term_symm " term " using " term : tactic

macro_rules
  | `(tactic| fx_stepstar_cast_source_type $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castSourceType $castEquality $chainStep)
  | `(tactic| fx_stepstar_cast_target_type $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castTargetType $castEquality $chainStep)
  | `(tactic| fx_stepstar_cast_source_term $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castSourceTerm $castEquality $chainStep)
  | `(tactic| fx_stepstar_cast_target_term $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castTargetTerm $castEquality $chainStep)
  | `(tactic| fx_stepstar_cast_source_type_symm $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castSourceType ($castEquality).symm $chainStep)
  | `(tactic| fx_stepstar_cast_target_type_symm $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castTargetType ($castEquality).symm $chainStep)
  | `(tactic| fx_stepstar_cast_source_term_symm $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castSourceTerm ($castEquality).symm $chainStep)
  | `(tactic| fx_stepstar_cast_target_term_symm $castEquality using $chainStep) =>
      `(tactic| exact LeanFX2.StepStar.castTargetTerm ($castEquality).symm $chainStep)

macro "fx_stepstar_cast_using " chainStep:term : tactic =>
  `(tactic|
    first
      | exact LeanFX2.StepStar.castSourceType _ $chainStep
      | exact LeanFX2.StepStar.castTargetType _ $chainStep
      | exact LeanFX2.StepStar.castSourceTerm _ $chainStep
      | exact LeanFX2.StepStar.castTargetTerm _ $chainStep)

/-! ## Conv cast transport -/

syntax "fx_conv_cast_source_type " term " using " term : tactic
syntax "fx_conv_cast_target_type " term " using " term : tactic
syntax "fx_conv_cast_source_term " term " using " term : tactic
syntax "fx_conv_cast_target_term " term " using " term : tactic

syntax "fx_conv_cast_source_type_symm " term " using " term : tactic
syntax "fx_conv_cast_target_type_symm " term " using " term : tactic
syntax "fx_conv_cast_source_term_symm " term " using " term : tactic
syntax "fx_conv_cast_target_term_symm " term " using " term : tactic

macro_rules
  | `(tactic| fx_conv_cast_source_type $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castSourceType $castEquality $convertibility)
  | `(tactic| fx_conv_cast_target_type $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castTargetType $castEquality $convertibility)
  | `(tactic| fx_conv_cast_source_term $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castSourceTerm $castEquality $convertibility)
  | `(tactic| fx_conv_cast_target_term $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castTargetTerm $castEquality $convertibility)
  | `(tactic| fx_conv_cast_source_type_symm $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castSourceType ($castEquality).symm $convertibility)
  | `(tactic| fx_conv_cast_target_type_symm $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castTargetType ($castEquality).symm $convertibility)
  | `(tactic| fx_conv_cast_source_term_symm $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castSourceTerm ($castEquality).symm $convertibility)
  | `(tactic| fx_conv_cast_target_term_symm $castEquality using $convertibility) =>
      `(tactic| exact LeanFX2.Conv.castTargetTerm ($castEquality).symm $convertibility)

macro "fx_conv_cast_using " convertibility:term : tactic =>
  `(tactic|
    first
      | exact LeanFX2.Conv.castSourceType _ $convertibility
      | exact LeanFX2.Conv.castTargetType _ $convertibility
      | exact LeanFX2.Conv.castSourceTerm _ $convertibility
      | exact LeanFX2.Conv.castTargetTerm _ $convertibility)

end LeanFX2.Tools.Tactics
