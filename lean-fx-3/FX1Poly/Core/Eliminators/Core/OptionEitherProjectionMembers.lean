import FX1Poly.Core.Eliminators.Core.OptionEitherConstructedProjector
import FX1Poly.Core.Eliminators.Match.MatchEliminatorNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion

/-! # FX1Poly/Core/OptionEitherProjectionMembers
    — the option/either projection reducibility clause (#1755 option/either residue resolver)

`sigmaProjectionMembers carrierC term := carrierC (fstCell term) ∧ carrierC (sndCell term)` makes the product
type's reducibility candidate carry component membership at ARBITRARY (non-normal) components, by FORWARD
closure of the carrier through the built-in `fst`/`snd` projections.  Option/either have no built-in projection
eliminator, but the sibling file `OptionEitherConstructedProjector` builds one (`optionProject` / `eitherProject`)
from the match eliminator + an identity branch.  This file is the option/either analogue of
`sigmaProjectionMembers`: the single-carrier projection clause read through that constructed projector.

  * `optionProjectionMembers carrierCandidate term := carrierCandidate (optionProject term)` — "the payload
    projection of `term` is a carrier member".
  * `_isReducibilityCandidate` — CR1/CR2/CR3.  CR1 reflects the projection's SN back through the projector
    (`scrutinee_isStronglyNormalizing_of_optionProject`).  CR2 lifts a scrutinee step under the projector
    (`optionProject_congScrutinee`) and carries the carrier forward.  CR3 reads off `IsNeutral.optionMatch`: a
    neutral scrutinee makes the projector neutral, its only reducts are scrutinee-congruences (the ι cases are
    killed by neutrality; the fixed normal dummy children admit no step), so the carrier's own CR3 applies.
  * `_componentOfReachesSome` / `eitherProjectionMembers_componentOfReachesInl` — ★ the residue resolvers: a
    member whose scrutinee reaches `optionSome value` / `eitherInl value` has `carrierCandidate value`, by
    FORWARD closure (`optionProject_forwardToPayload`) — NO backward closure, NO normality assumption on the
    payload.  Exactly the `someBranchMemberIfReachesSome` / `leftBranchMemberIfReachesInl` reach-residue the
    native optionMatch/eitherMatch elim fundamental-theorem rows need.

## Zero-axiom verification

Mirrors `sigmaProjectionMembers`: the candidate fields dispatch to the carrier candidate's CR1/CR2/CR3 through
the projector's shipped reduction/neutrality lemmas; the dummy-branch no-step facts are `Step.from_lam` +
`noStep_optionNone` + `noStep_var`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open StepStar

/-- **One scrutinee step lifts under `optionProject`.**  `Step scrutinee reduct → Step (optionProject scrutinee)
(optionProject reduct)` — congruence into the projector's scrutinee child (the last of the 4-child spine). -/
private theorem optionProject_congScrutinee {scope : Nat} {scrutinee reduct : RawTerm scope}
    (step : Step scrutinee reduct) : Step (optionProject scrutinee) (optionProject reduct) :=
  Step.cong .gen_optionMatch ()
    (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ step))))

/-- **One scrutinee step lifts under `eitherProject`.**  The Either twin of `optionProject_congScrutinee`. -/
private theorem eitherProject_congScrutinee {scope : Nat} {scrutinee reduct : RawTerm scope}
    (step : Step scrutinee reduct) : Step (eitherProject scrutinee) (eitherProject reduct) :=
  Step.cong .gen_eitherMatch ()
    (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ step))))

/-- **Reverse SN through `optionProject`.**  `SN (optionProject scrutinee) → SN scrutinee` — an `Acc`-descent:
each scrutinee step lifts to a projector step (`optionProject_congScrutinee`), so the projector's accessibility
predecessors include every lifted scrutinee step.  Mirrors `scrutinee_isStronglyNormalizing_of_fstCell`. -/
private theorem scrutinee_isStronglyNormalizing_of_optionProject {scope : Nat} {scrutinee : RawTerm scope}
    (projectorTerminates : IsStronglyNormalizing (optionProject scrutinee)) :
    IsStronglyNormalizing scrutinee := by
  suffices general :
      ∀ {projectorTerm : RawTerm scope}, Acc StepSuccessor projectorTerm →
        ∀ {currentScrutinee : RawTerm scope}, projectorTerm = optionProject currentScrutinee →
          Acc StepSuccessor currentScrutinee from
    general projectorTerminates rfl
  intro projectorTerm projectorAccessible
  induction projectorAccessible with
  | intro _projectorWitness _projectorPredecessors projectorInductiveHypothesis =>
      intro currentScrutinee witnessEq
      subst witnessEq
      apply Acc.intro
      intro scrutineeAfter scrutineeStep
      exact projectorInductiveHypothesis (optionProject scrutineeAfter)
        (optionProject_congScrutinee scrutineeStep) rfl

/-- **Reverse SN through `eitherProject`.**  The Either twin of `scrutinee_isStronglyNormalizing_of_optionProject`. -/
private theorem scrutinee_isStronglyNormalizing_of_eitherProject {scope : Nat} {scrutinee : RawTerm scope}
    (projectorTerminates : IsStronglyNormalizing (eitherProject scrutinee)) :
    IsStronglyNormalizing scrutinee := by
  suffices general :
      ∀ {projectorTerm : RawTerm scope}, Acc StepSuccessor projectorTerm →
        ∀ {currentScrutinee : RawTerm scope}, projectorTerm = eitherProject currentScrutinee →
          Acc StepSuccessor currentScrutinee from
    general projectorTerminates rfl
  intro projectorTerm projectorAccessible
  induction projectorAccessible with
  | intro _projectorWitness _projectorPredecessors projectorInductiveHypothesis =>
      intro currentScrutinee witnessEq
      subst witnessEq
      apply Acc.intro
      intro scrutineeAfter scrutineeStep
      exact projectorInductiveHypothesis (eitherProject scrutineeAfter)
        (eitherProject_congScrutinee scrutineeStep) rfl

/-- **The projector's identity branch admits no step.**  `lam projectorDummy (var 0)`: a lam steps only by
congruence into its annotation (`projectorDummy = optionNone`, killed by `noStep_optionNone`) or its body
(`var 0`, killed by `noStep_var`).  Kills the some/left-branch congruence case of the projector step inversion. -/
private theorem projectorIdentityBranch_noStep {scope : Nat} {target : RawTerm scope}
    (step : Step projectorIdentityBranch target) : False := by
  rcases Step.from_lam step with
    ⟨_domainAfter, _, domainStep⟩ | ⟨_bodyAfter, _, bodyStep⟩
  · exact noStep_optionNone domainStep
  · exact noStep_var _ bodyStep

/-- **The option projection clause.**  `carrierCandidate (optionProject term)` — the payload projection of
`term` is a carrier member.  The single-carrier Girard candidate read through the constructed `optionProject`. -/
def optionProjectionMembers {scope : Nat} (carrierCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  carrierCandidate (optionProject term)

/-- **The either projection clause.**  `carrierCandidate (eitherProject term)` — the inl-payload projection of
`term` is a carrier member. -/
def eitherProjectionMembers {scope : Nat} (carrierCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  carrierCandidate (eitherProject term)

/-- **★ The option projection clause is a Girard reducibility candidate.**  CR1 reflects the projector's SN back
through `scrutinee_isStronglyNormalizing_of_optionProject`; CR2 lifts a scrutinee step (`optionProject_congScrutinee`)
and the carrier carries it forward; CR3 makes the projector neutral (`IsNeutral.optionMatch`) — its reducts are
exactly the scrutinee-congruences (ι killed by neutrality, dummy children normal), so the carrier's CR3 applies. -/
theorem optionProjectionMembers_isReducibilityCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate) :
    IsReducibilityCandidate (optionProjectionMembers carrierCandidate) where
  stronglyNormalizing := fun member =>
    scrutinee_isStronglyNormalizing_of_optionProject (carrierIsCandidate.stronglyNormalizing member)
  closedUnderStep := fun member step =>
    carrierIsCandidate.closedUnderStep member (optionProject_congScrutinee step)
  neutralExpansion := fun scrutineeNeutral reductsMembers =>
    carrierIsCandidate.neutralExpansion (IsNeutral.optionMatch scrutineeNeutral) (fun reduct step => by
      rcases Step.from_optionMatch step with
        ⟨scrutineeIsNone, _⟩ |
        ⟨_value, scrutineeIsSome, _⟩ |
        ⟨_motiveAfter, _, motiveStep⟩ |
        ⟨_noneAfter, _, noneStep⟩ |
        ⟨_someAfter, _, someStep⟩ |
        ⟨scrutineeAfter, targetEquation, scrutineeStep⟩
      · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsNone)
          scrutineeNeutral.rootGenerator_ne_optionNone
      · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsSome)
          scrutineeNeutral.rootGenerator_ne_optionSome
      · exact (noStep_optionNone motiveStep).elim
      · exact (noStep_optionNone noneStep).elim
      · exact (projectorIdentityBranch_noStep someStep).elim
      · rw [targetEquation]; exact reductsMembers scrutineeAfter scrutineeStep)

/-- **★ The either projection clause is a Girard reducibility candidate.**  The Either twin of
`optionProjectionMembers_isReducibilityCandidate` (both ι cases killed by neutrality, the left/right branch
congruences killed by the dummy/identity-branch no-step facts). -/
theorem eitherProjectionMembers_isReducibilityCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate) :
    IsReducibilityCandidate (eitherProjectionMembers carrierCandidate) where
  stronglyNormalizing := fun member =>
    scrutinee_isStronglyNormalizing_of_eitherProject (carrierIsCandidate.stronglyNormalizing member)
  closedUnderStep := fun member step =>
    carrierIsCandidate.closedUnderStep member (eitherProject_congScrutinee step)
  neutralExpansion := fun scrutineeNeutral reductsMembers =>
    carrierIsCandidate.neutralExpansion (IsNeutral.eitherMatch scrutineeNeutral) (fun reduct step => by
      rcases Step.from_eitherMatch step with
        ⟨_value, scrutineeIsInl, _⟩ |
        ⟨_value, scrutineeIsInr, _⟩ |
        ⟨_motiveAfter, _, motiveStep⟩ |
        ⟨_leftAfter, _, leftStep⟩ |
        ⟨_rightAfter, _, rightStep⟩ |
        ⟨scrutineeAfter, targetEquation, scrutineeStep⟩
      · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsInl)
          scrutineeNeutral.rootGenerator_ne_eitherInl
      · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsInr)
          scrutineeNeutral.rootGenerator_ne_eitherInr
      · exact (noStep_optionNone motiveStep).elim
      · exact (projectorIdentityBranch_noStep leftStep).elim
      · exact (noStep_optionNone rightStep).elim
      · rw [targetEquation]; exact reductsMembers scrutineeAfter scrutineeStep)

/-- **★ Reached-`some` payload membership — the option residue resolver, by FORWARD closure.**  When a member's
scrutinee reaches `optionSome value`, the payload is a carrier member: `optionProject term` multi-steps to
`value` (`optionProject_forwardToPayload`), and the clause carries forward by `closedUnderStepStar`.  The
discharge the native optionMatch elim FT row's `someBranchMemberIfReachesSome` residue needs — with NO backward
closure and NO assumption that `value` is normal. -/
theorem optionProjectionMembers_componentOfReachesSome {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate)
    {term value : RawTerm scope}
    (member : optionProjectionMembers carrierCandidate term)
    (reachesSome : StepStar term (.mkGen .gen_optionSome () (.childCons value .childNil))) :
    carrierCandidate value :=
  carrierIsCandidate.closedUnderStepStar (optionProject_forwardToPayload reachesSome) member

/-- **★ Reached-`inl` payload membership — the either residue resolver, by FORWARD closure.**  Symmetric to
`optionProjectionMembers_componentOfReachesSome`, discharging the native eitherMatch elim FT row's
`leftBranchMemberIfReachesInl` residue. -/
theorem eitherProjectionMembers_componentOfReachesInl {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate)
    {term value : RawTerm scope}
    (member : eitherProjectionMembers carrierCandidate term)
    (reachesInl : StepStar term (.mkGen .gen_eitherInl () (.childCons value .childNil))) :
    carrierCandidate value :=
  carrierIsCandidate.closedUnderStepStar (eitherProject_forwardToInlPayload reachesInl) member

end FX1Poly.Core
