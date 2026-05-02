import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Pointwise

/-! # Reduction/Compat — rename + subst compatibility

Renaming and substitution preserve every reduction relation:
* `Step` (single step)
* `Step.par` (parallel reduction)
* `StepStar` (multi-step)
* `Conv` (definitional conversion)

## The big simplification

In lean-fx, `Step.subst_compatible` (and its parallel variants) had
to thread `RawConsistent termSubstitution` because `subst0_term`
needed it.  This propagated through ~17 files as a viral hypothesis.

In lean-fx-2, `RawConsistent` is *definitional* (every TermSubst is
automatically raw-consistent because forRaw is constrained by Term
values' raw indices).  No threading needed.  Subst compat proofs are
~30% smaller.

## Contents

### Single-step (Step)

```lean
theorem Step.rename_compatible {ρt : TermRenaming Γ Δ ρ}
    (s : Step beforeTerm afterTerm) :
    Step (Term.rename ρt beforeTerm) (Term.rename ρt afterTerm)
```

Structural induction on Step.  Cong cases are direct.  β-arms use
`Term.rename_subst0` commute lemma from `Term/Pointwise.lean`.

```lean
theorem Step.subst_compatible {σ : TermSubst Γ Δ s}
    (step : Step beforeTerm afterTerm) :
    Step (Term.subst σ beforeTerm) (Term.subst σ afterTerm)
```

Structural induction on Step.  No `RawConsistent` parameter — the
TermSubst's structural raw-consistency is enough.

### Parallel reduction (Step.par)

```lean
theorem Step.par.rename_compatible : Step.par t1 t2 → Step.par (rename t1) (rename t2)
theorem Step.par.subst_compatible  : Step.par t1 t2 → Step.par (subst t1) (subst t2)
```

Same structure as Step, lifted to parallel.

### Multi-step (StepStar)

Both via `StepStar.mapStep`:

```lean
theorem StepStar.rename_compatible : StepStar t1 t2 → StepStar (rename t1) (rename t2) :=
  StepStar.mapStep (Term.rename ρt) Step.rename_compatible

theorem StepStar.subst_compatible : StepStar t1 t2 → StepStar (subst t1) (subst t2) :=
  StepStar.mapStep (Term.subst σ) Step.subst_compatible
```

### Conv

Both via `mapStep` on each existential chain:

```lean
theorem Conv.rename_compatible (h : Conv t1 t2) : Conv (rename t1) (rename t2) := by
  obtain ⟨_, t', s1, s2⟩ := h
  exact ⟨_, Term.rename ρt t',
         StepStar.rename_compatible s1, StepStar.rename_compatible s2⟩
```

## Dependencies

* `Reduction/Step.lean`, `Reduction/StepStar.lean`, `Reduction/Conv.lean`,
  `Reduction/ParRed.lean`
* `Term/Pointwise.lean` — for subst-rename commute lemmas

## Downstream consumers

* `Confluence/*` — uses Step.par.subst_compatible in cd_lemma
* `Algo/Eval.lean` — fuel-bounded eval composes substitutions

## Diff from lean-fx

* Single file `Compat.lean` (lean-fx had `Reduction/{Rename,Subst,Compatible,ParCompatible}.lean` = 4 files)
* No `RawConsistent` threading
* No paired-predicate `*_compatible_witnessed` variants
* β-arms ~50% smaller (no W9.B1.1/B1.2 `resultEq` scaffolding)

Target: ~600 lines (vs ~2500 lines across 4 lean-fx files).
-/

namespace LeanFX2

end LeanFX2
