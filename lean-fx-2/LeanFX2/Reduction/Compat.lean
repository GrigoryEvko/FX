import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst
import LeanFX2.Reduction.Compat.Cubical
import LeanFX2.Reduction.Compat.HoTT
import LeanFX2.Reduction.Compat.Effects
import LeanFX2.Reduction.Compat.Misc
import LeanFX2.Reduction.Compat.TypeCodes

/-! # Reduction/Compat — rename + subst compatibility (umbrella)

Renaming and substitution preserve every reduction relation:
* `Step` (single step)
* `Step.par` (parallel reduction)
* `StepStar` (multi-step) — via `mapStep`
* `Conv` (definitional conversion) — via `mapStep`

## Module layout (REFACTOR-COMPAT #1550)

The 28 per-cong typed compatibility theorems live in 4 sibling
sub-modules grouped by ctor family.  This umbrella re-exports
all of them via the imports above and ships only the small
raw-layer compatibility API (lines below).  Downstream files
that `import LeanFX2.Reduction.Compat` keep working unchanged.

* `Compat/Cubical.lean` — 9 ctors (interval/glue/path/hcomp/transp/pathLam)
* `Compat/HoTT.lean` — 11 ctors (oeqRefl/J/Funext/equivApp/Intro/IntroHet/
  uaIntroHet/refl/funextRefl/funextReflAtId/funextIntroHet)
* `Compat/Effects.lean` — 7 ctors (refine/codata/session/effect)
* `Compat/Misc.lean` — 5 ctors (cumulUpInner/recordProj/Intro/idStrict{Refl,Rec})
* `Compat/TypeCodes.lean` — 10 ctors (CUMUL-2.4 typed type-code constructors:
  arrow/piTy/sigmaTy/product/sum/list/option/either/id/equivCode)

## The big simplification (from lean-fx)

In lean-fx, β-arms required a separate `RawConsistent` hypothesis
threaded through ~17 files because `Term.subst0_term` consulted the
raw side via a `forRaw` field that could be inconsistent with the
typed `forTy`.  In lean-fx-2, `RawTerm scope` is a Term type-level
index — every typed Term is automatically raw-consistent — so no
threading is needed.  Subst-compat proofs are ~30% smaller.

## D2.10 typed compositional compat (per-cong)

The per-cong typed compat lemmas in the sub-modules ship as
compositional theorems: each takes the renamed/substituted
inner Step.par as a HYPOTHESIS and produces the outer Step.par
by applying the corresponding cong constructor.  This pattern
avoids needing a typed `Step.par.rename` / `Step.par.subst`
induction theorem (which would require ~500 LoC of dep-cast
threading).  The compositional approach lets confluence
consumers obtain the per-cong compat by combining the
inner-step compat (proved separately) with these single-rule
combinators.
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
