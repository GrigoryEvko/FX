import FX1Poly.Core.StepRename
import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StrongNormalizationRename
    — strong normalization reflects along renaming

If a renamed term is strongly normalizing, so is the term it was renamed from.
This is the *reflection* direction of SN under renaming, and it needs only
*Step preservation* (`Step.rename`: `t ↝ t'` lifts to
`rename ρ t ↝ rename ρ t'`), which holds for every renaming: any infinite
reduction sequence out of the source maps forward to one out of the renamed
term, so the renamed term's accessibility transfers back down to the source.

The opposite (forward) direction — `SN t → SN (rename ρ t)` — would need Step
*reflection* (every reduct of `rename ρ t` comes from a reduct of `t`), which
requires `ρ` injective; that direction is not proved in this file.

## Why this lemma

It is sub-lemma (d) of the arrow reducibility candidate: the candidate's CR1
feeds a *fresh* argument variable, which forces a weakening of the function
(`weaken f = rename` of the weakening renaming) and then must reflect the
resulting `SN (weaken f)` back to `SN f` — exactly this reflection.  It is also
the SN half of candidate weakening/monotonicity (the Kripke-indexed candidate
family the arrow case needs).

## Zero-axiom verification

`Acc` induction generalized over the renamed term (so the recursion's index is
a variable) plus the `Step.rename` lift — no `axiom`, `sorry`, `propext`,
`Quot.sound`.  Swept by `#audit_namespace FX1Poly.Core` in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- Strong normalization reflects along renaming: if `RawTerm.rename ρ
sourceTerm` is strongly normalizing then so is `sourceTerm`.  Each source step
lifts forward to a renamed step via `Step.rename`, so the renamed term's
accessibility transfers to the source.  The `Acc` induction is generalized over
the renamed term so the recursion's index is a variable. -/
theorem isStronglyNormalizing_of_rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope}
    (renamedTerminates :
      IsStronglyNormalizing (RawTerm.rename rawRenaming sourceTerm)) :
    IsStronglyNormalizing sourceTerm := by
  suffices general :
      ∀ {renamedWitness : RawTerm targetScope},
        Acc StepSuccessor renamedWitness →
          ∀ {currentSource : RawTerm sourceScope},
            renamedWitness = RawTerm.rename rawRenaming currentSource →
            Acc StepSuccessor currentSource from
    general renamedTerminates rfl
  intro renamedWitness renamedAccessible
  induction renamedAccessible with
  | intro renamedFocus _renamedPredecessors renamedInductiveHypothesis =>
      intro currentSource witnessEq
      subst witnessEq
      apply Acc.intro
      intro sourceAfter sourceStep
      have renamedStep :
          Step (RawTerm.rename rawRenaming currentSource)
            (RawTerm.rename rawRenaming sourceAfter) :=
        Step.rename rawRenaming sourceStep
      exact renamedInductiveHypothesis
        (RawTerm.rename rawRenaming sourceAfter) renamedStep rfl

end StepStar
end FX1Poly.Core
