import LeanFX2.Reduction.Step

/-! # Reduction/StepStar — reflexive-transitive closure of Step

```lean
inductive StepStar :
    Term ctx ty rawSrc → Term ctx ty rawTgt → Prop
  | refl (t) : StepStar t t
  | step : Step t1 t2 → StepStar t2 t3 → StepStar t1 t3
```

## Contents

* `StepStar` inductive
* `StepStar.append` — concatenate two chains
* `StepStar.snoc` — append a single Step at the end
* `StepStar.lift_step (s : Step a b) : StepStar a b` — single-step
  → multi-step
* `StepStar.cast{Source,Target,Both}` — type-equation transport

### mapStep — the cong-rule lifter

```lean
def StepStar.mapStep {sourceTy : Ctx m level scope}
    (mapTerm : ∀ {ctx ty raw}, Term ctx ty raw → Term ctx' ty' raw')
    (mapSingleStep : ∀ {a b}, Step a b → Step (mapTerm a) (mapTerm b))
    {a b} (chain : StepStar a b) : StepStar (mapTerm a) (mapTerm b)
```

This single lifter replaces ~13 cong rules in lean-fx (StepStar.app_cong,
StepStar.lam_cong, etc.) with 1-line corollary applications.
Per lean-fx's `feedback_lean_mapStep_pattern.md` — verified zero-axiom
across 80+ refactored cong theorems.

### Cong rule shortcuts (each 1-line via mapStep)

* `StepStar.app_cong_left/right`
* `StepStar.lam_cong`, `StepStar.lamPi_cong`
* `StepStar.appPi_cong_left/right`
* `StepStar.pair_cong_left/right`
* `StepStar.fst_cong`, `StepStar.snd_cong`
* (eliminators: boolElim, natElim, listElim, etc. — analogous)
* `StepStar.idJ_cong_base/witness`

## Dependencies

* `Reduction/Step.lean`

## Downstream consumers

* `Reduction/Conv.lean` — Conv = ∃ middle, both sides StepStar
* `Reduction/Compatible.lean` — StepStar.rename/subst_compatible via mapStep
* `Confluence/ChurchRosser.lean` — confluence statement uses StepStar

## Implementation plan (Phase 3)

Port from `lean-fx/LeanFX/Syntax/Reduction/StepStar.lean` (~282 lines):
* Keep mapStep as the single lifter
* All cong-rule shortcuts via mapStep
* Verify cast helpers stay zero-axiom

Target: ~250 lines.
-/

namespace LeanFX2

end LeanFX2
