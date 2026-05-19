import LeanFX2.Reduction.RawParCompatible.NamedCompatibility
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

The per-cong typed compatibility theorems live in sibling
sub-modules grouped by ctor family. This umbrella re-exports
all of them via the imports above and also re-exports the small
raw-layer compatibility API from
`Reduction/RawParCompatible/NamedCompatibility.lean`. Downstream
files that `import LeanFX2.Reduction.Compat` keep working unchanged.

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

end LeanFX2
