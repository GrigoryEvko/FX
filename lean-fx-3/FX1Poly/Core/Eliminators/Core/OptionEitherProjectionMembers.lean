import FX1Poly.Core.Eliminators.Core.OptionEitherConstructedProjector
import FX1Poly.Core.Eliminators.Match.MatchEliminatorNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationDeterminism
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSpineExpansion
import FX1Poly.Core.Metatheory.Reducibility.Core.HeadExpansionClosure
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeHeadExpansion

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

/-- **One scrutinee step lifts under `eitherProjectRight`.**  The inr twin of `eitherProject_congScrutinee` —
the scrutinee is still the last (4th) child, so the same `StepChildren` path. -/
private theorem eitherProjectRight_congScrutinee {scope : Nat} {scrutinee reduct : RawTerm scope}
    (step : Step scrutinee reduct) : Step (eitherProjectRight scrutinee) (eitherProjectRight reduct) :=
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

/-- **Reverse SN through `eitherProjectRight`.**  The inr twin of
`scrutinee_isStronglyNormalizing_of_eitherProject`. -/
private theorem scrutinee_isStronglyNormalizing_of_eitherProjectRight {scope : Nat} {scrutinee : RawTerm scope}
    (projectorTerminates : IsStronglyNormalizing (eitherProjectRight scrutinee)) :
    IsStronglyNormalizing scrutinee := by
  suffices general :
      ∀ {projectorTerm : RawTerm scope}, Acc StepSuccessor projectorTerm →
        ∀ {currentScrutinee : RawTerm scope}, projectorTerm = eitherProjectRight currentScrutinee →
          Acc StepSuccessor currentScrutinee from
    general projectorTerminates rfl
  intro projectorTerm projectorAccessible
  induction projectorAccessible with
  | intro _projectorWitness _projectorPredecessors projectorInductiveHypothesis =>
      intro currentScrutinee witnessEq
      subst witnessEq
      apply Acc.intro
      intro scrutineeAfter scrutineeStep
      exact projectorInductiveHypothesis (eitherProjectRight scrutineeAfter)
        (eitherProjectRight_congScrutinee scrutineeStep) rfl

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

/-- **The either RIGHT projection clause.**  `carrierCandidate (eitherProjectRight term)` — the inr-payload
projection of `term` is a carrier member.  The inr twin of `eitherProjectionMembers`; at the conjoined either
candidate this rides the `secondCandidate` carrier (the inr arm's type). -/
def eitherProjectionMembersRight {scope : Nat} (carrierCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  carrierCandidate (eitherProjectRight term)

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

/-- **★ The either RIGHT projection clause is a Girard reducibility candidate.**  The inr twin of
`eitherProjectionMembers_isReducibilityCandidate`: in the CR3 neutral-expansion inversion the LEFT branch is now
the fixed dummy (killed by `noStep_optionNone`) and the RIGHT branch is the identity lambda (killed by
`projectorIdentityBranch_noStep`). -/
theorem eitherProjectionMembersRight_isReducibilityCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate) :
    IsReducibilityCandidate (eitherProjectionMembersRight carrierCandidate) where
  stronglyNormalizing := fun member =>
    scrutinee_isStronglyNormalizing_of_eitherProjectRight (carrierIsCandidate.stronglyNormalizing member)
  closedUnderStep := fun member step =>
    carrierIsCandidate.closedUnderStep member (eitherProjectRight_congScrutinee step)
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
      · exact (noStep_optionNone leftStep).elim
      · exact (projectorIdentityBranch_noStep rightStep).elim
      · rw [targetEquation]; exact reductsMembers scrutineeAfter scrutineeStep)

/-- **The either inl-projection clause is forward-closed under one `Step`** (CR2, LEG-FREE).  Needs only the
carrier's forward-STAR closure, NOT full candidacy: the single scrutinee step lifts under `eitherProject`
(`eitherProject_congScrutinee`) to a single projector step, and the carrier carries membership forward along
it.  The leg-free CR2 the conjoined coproduct candidate's `_closedUnderStep` needs from the inl conjunct — at
the denote `memberForwardClosed` consumer the carrier induction hypothesis is exactly forward-star closure, so
a full-candidacy requirement would be unsatisfiable (the `sigmaProjectionMembers_closedUnderStep` story for
the inl projection). -/
theorem eitherProjectionMembers_closedUnderStep {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierForwardStar : ∀ {origin destination : RawTerm scope},
        StepStar origin destination → carrierCandidate origin → carrierCandidate destination)
    {term reduct : RawTerm scope}
    (member : eitherProjectionMembers carrierCandidate term) (step : Step term reduct) :
    eitherProjectionMembers carrierCandidate reduct :=
  carrierForwardStar (StepStar.single (eitherProject_congScrutinee step)) member

/-- **The either inr-projection clause is forward-closed under one `Step`** (CR2, LEG-FREE).  The inr twin of
`eitherProjectionMembers_closedUnderStep`, lifting the scrutinee step under `eitherProjectRight`
(`eitherProjectRight_congScrutinee`).  The leg-free CR2 the conjoined coproduct candidate's `_closedUnderStep`
needs from the inr conjunct. -/
theorem eitherProjectionMembersRight_closedUnderStep {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierForwardStar : ∀ {origin destination : RawTerm scope},
        StepStar origin destination → carrierCandidate origin → carrierCandidate destination)
    {term reduct : RawTerm scope}
    (member : eitherProjectionMembersRight carrierCandidate term) (step : Step term reduct) :
    eitherProjectionMembersRight carrierCandidate reduct :=
  carrierForwardStar (StepStar.single (eitherProjectRight_congScrutinee step)) member

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

/-- **★ Reached-`inr` payload membership — the either RIGHT residue resolver, by FORWARD closure.**  Symmetric
to `eitherProjectionMembers_componentOfReachesInl`, discharging the native eitherMatch elim FT row's
`rightBranchMemberIfReachesInr` residue at an ARBITRARY (possibly non-normal) payload. -/
theorem eitherProjectionMembersRight_componentOfReachesInr {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierIsCandidate : IsReducibilityCandidate carrierCandidate)
    {term value : RawTerm scope}
    (member : eitherProjectionMembersRight carrierCandidate term)
    (reachesInr : StepStar term (.mkGen .gen_eitherInr () (.childCons value .childNil))) :
    carrierCandidate value :=
  carrierIsCandidate.closedUnderStepStar (eitherProjectRight_forwardToInrPayload reachesInr) member

/-- **The projector's identity-branch application is SN when its argument is.**  `app (lam projectorDummy
(var 0)) value` β-reduces to `subst0 (var 0) value = value`; the body `var 0` is a normal leaf and the domain
`projectorDummy = optionNone` is normal, so `appLam_isStronglyNormalizing_of_normal_body_contractum` applies
with the contractum SN supplied by `value` through `RawTerm.subst0_var_zero`.  The some/left/right-branch
contractum SN the projector forward-SN lemmas feed to the match SN engines. -/
private theorem projectorIdentityBranch_app_isStronglyNormalizing_of_argument {scope : Nat}
    {value : RawTerm scope} (valueStronglyNormalizing : IsStronglyNormalizing value) :
    IsStronglyNormalizing
      (.mkGen .gen_app () (.childCons projectorIdentityBranch (.childCons value .childNil))) :=
  appLam_isStronglyNormalizing_of_normal_body_contractum
    (fun _targetBody bodyStep => noStep_var _ bodyStep)
    (fun {currentArgument} currentArgumentStronglyNormalizing => by
      rw [RawTerm.subst0_var_zero]; exact currentArgumentStronglyNormalizing)
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    valueStronglyNormalizing

/-- **★ `optionProject scrutinee` is strongly normalizing when the scrutinee is.**  The projector is `optionMatch`
over fixed normal dummies plus the identity some-branch; `optionMatch_isStronglyNormalizing_of_strongly_normalizing
_branches` needs only the some-branch contractum SN (the none-branch is selected, not applied) —
`projectorIdentityBranch_app_isStronglyNormalizing_of_argument` — alongside the (normal) motive / none / some SN.
The forward-SN that the option projection clause's member weak-head expansion threads as the source-SN witness. -/
theorem optionProject_isStronglyNormalizing {scope : Nat} {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing (optionProject scrutinee) :=
  optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches
    (fun _value valueStronglyNormalizing =>
      projectorIdentityBranch_app_isStronglyNormalizing_of_argument valueStronglyNormalizing)
    scrutineeStronglyNormalizing
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => projectorIdentityBranch_noStep step))

/-- **★ The option projection clause is closed under member weak-head expansion** (WHE).  A weak-head step of
`source` lifts under the projector to a weak-head step (`WeakHeadStep.scrutineeOptionMatch`); the carrier
candidate's own weak-head expansion (`carrierHeadExpand`, the interface the projection FT engines take) carries
membership back, with `optionProject source` strongly normalizing from `source` by `optionProject_isStronglyNormalizing`.
The option analogue of `sigmaProjectionMembers_memberWeakHeadExpansion`. -/
theorem optionProjectionMembers_memberWeakHeadExpansion {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : optionProjectionMembers carrierCandidate reduct) :
    optionProjectionMembers carrierCandidate source :=
  carrierHeadExpand (WeakHeadStep.scrutineeOptionMatch weakHeadStep) reductMember
    (optionProject_isStronglyNormalizing sourceStronglyNormalizing)

/-- **★ The option projection clause is β-spine head-expansion-closed** (the Π-codomain-ready property).  A spined
β-redex whose β-contractum has a reducible payload projection has one itself: the β-spine redex weak-head-steps to
its contractum (`WeakHeadStep.betaSpine`), so this is `optionProjectionMembers_memberWeakHeadExpansion` at that
weak-head step — the source SN reflects the contractum's projector SN back over the β-spine by
`betaSpineHeadExpansion`.  Takes the carrier's GENERAL weak-head expansion, supplied STANDALONE at the Typed denote
level by `ReducibleTypeAtBounded.memberWeakHeadExpansion`.  The option analogue of
`sigmaProjectionMembers_headExpansionClosed`. -/
theorem optionProjectionMembers_headExpansionClosed {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierStronglyNormalizing : ∀ {member : RawTerm scope},
        carrierCandidate member → IsStronglyNormalizing member)
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex) :
    HeadExpansionClosed (optionProjectionMembers carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  exact optionProjectionMembers_memberWeakHeadExpansion carrierHeadExpand
    WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN
      (scrutinee_isStronglyNormalizing_of_optionProject (carrierStronglyNormalizing contractumMember)))
    contractumMember

/-- **The dummy branch applied to an SN argument is SN.**  `app projectorDummy value` — where `projectorDummy =
optionNone` is a normal CONSTRUCTOR (not a lambda) — is a stuck application; its only reducts are
argument-congruences (β is impossible because the function is not a `lam`, and the function `optionNone` itself
admits no step).  Accessibility induction on the argument then closes it.  Unlike `app idLam value`, no
contractum exists; this is the right-branch (`eitherProject`) / left-branch (`eitherProjectRight`) dummy
contractum SN the either projector forward-SN lemmas feed to `eitherMatch_isStronglyNormalizing_of_strongly
_normalizing_branches`. -/
private theorem projectorDummy_app_isStronglyNormalizing_of_argument {scope : Nat}
    {value : RawTerm scope} (valueStronglyNormalizing : IsStronglyNormalizing value) :
    IsStronglyNormalizing
      (.mkGen .gen_app () (.childCons projectorDummy (.childCons value .childNil))) := by
  induction valueStronglyNormalizing with
  | intro currentValue _currentValueSuccessors valueInductiveHypothesis =>
    apply Acc.intro
    intro target step
    rcases Step.from_app step with
      ⟨_domainAnn, _body, functionIsLam, _targetEquation⟩ |
      ⟨_functionAfter, _targetEquation, functionStep⟩ |
      ⟨valueAfter, targetEquation, valueStep⟩
    · exact Generator.noConfusion (congrArg RawTerm.rootGenerator functionIsLam)
    · exact (noStep_optionNone functionStep).elim
    · subst targetEquation; exact valueInductiveHypothesis valueAfter valueStep

/-- **★ `eitherProject scrutinee` is strongly normalizing when the scrutinee is.**  The either analogue of
`optionProject_isStronglyNormalizing`; `eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches` needs
BOTH branch contractum premises — the LEFT (identity) branch via `projectorIdentityBranch_app_isStronglyNormalizing
_of_argument`, the RIGHT (dummy) branch via `projectorDummy_app_isStronglyNormalizing_of_argument`. -/
theorem eitherProject_isStronglyNormalizing {scope : Nat} {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing (eitherProject scrutinee) :=
  eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches
    (fun _value valueStronglyNormalizing =>
      projectorIdentityBranch_app_isStronglyNormalizing_of_argument valueStronglyNormalizing)
    (fun _value valueStronglyNormalizing =>
      projectorDummy_app_isStronglyNormalizing_of_argument valueStronglyNormalizing)
    scrutineeStronglyNormalizing
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => projectorIdentityBranch_noStep step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))

/-- **★ `eitherProjectRight scrutinee` is strongly normalizing when the scrutinee is.**  The inr twin of
`eitherProject_isStronglyNormalizing`: the LEFT branch is now the dummy (`projectorDummy_app_…`) and the RIGHT
branch is the identity lambda (`projectorIdentityBranch_app_…`); the branch-SN witnesses swap accordingly. -/
theorem eitherProjectRight_isStronglyNormalizing {scope : Nat} {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing (eitherProjectRight scrutinee) :=
  eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches
    (fun _value valueStronglyNormalizing =>
      projectorDummy_app_isStronglyNormalizing_of_argument valueStronglyNormalizing)
    (fun _value valueStronglyNormalizing =>
      projectorIdentityBranch_app_isStronglyNormalizing_of_argument valueStronglyNormalizing)
    scrutineeStronglyNormalizing
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_optionNone step))
    (isStronglyNormalizing_of_noStep (fun _targetTerm step => projectorIdentityBranch_noStep step))

/-- **★ The either projection clause is closed under member weak-head expansion** (WHE).  The Either twin of
`optionProjectionMembers_memberWeakHeadExpansion`: a weak-head step lifts under the projector via
`WeakHeadStep.scrutineeEitherMatch`; source SN from `eitherProject_isStronglyNormalizing`. -/
theorem eitherProjectionMembers_memberWeakHeadExpansion {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : eitherProjectionMembers carrierCandidate reduct) :
    eitherProjectionMembers carrierCandidate source :=
  carrierHeadExpand (WeakHeadStep.scrutineeEitherMatch weakHeadStep) reductMember
    (eitherProject_isStronglyNormalizing sourceStronglyNormalizing)

/-- **★ The either RIGHT projection clause is closed under member weak-head expansion** (WHE).  The inr twin —
the projector is `eitherProjectRight`, source SN from `eitherProjectRight_isStronglyNormalizing`. -/
theorem eitherProjectionMembersRight_memberWeakHeadExpansion {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : eitherProjectionMembersRight carrierCandidate reduct) :
    eitherProjectionMembersRight carrierCandidate source :=
  carrierHeadExpand (WeakHeadStep.scrutineeEitherMatch weakHeadStep) reductMember
    (eitherProjectRight_isStronglyNormalizing sourceStronglyNormalizing)

/-- **★ The either projection clause is β-spine head-expansion-closed.**  The Either twin of
`optionProjectionMembers_headExpansionClosed` — member-WHE at `WeakHeadStep.betaSpine`, source SN reflected
through `scrutinee_isStronglyNormalizing_of_eitherProject`. -/
theorem eitherProjectionMembers_headExpansionClosed {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierStronglyNormalizing : ∀ {member : RawTerm scope},
        carrierCandidate member → IsStronglyNormalizing member)
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex) :
    HeadExpansionClosed (eitherProjectionMembers carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  exact eitherProjectionMembers_memberWeakHeadExpansion carrierHeadExpand
    WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN
      (scrutinee_isStronglyNormalizing_of_eitherProject (carrierStronglyNormalizing contractumMember)))
    contractumMember

/-- **★ The either RIGHT projection clause is β-spine head-expansion-closed.**  The inr twin — projector
`eitherProjectRight`, source SN reflected through `scrutinee_isStronglyNormalizing_of_eitherProjectRight`. -/
theorem eitherProjectionMembersRight_headExpansionClosed {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierStronglyNormalizing : ∀ {member : RawTerm scope},
        carrierCandidate member → IsStronglyNormalizing member)
    (carrierHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → carrierCandidate contractum →
        IsStronglyNormalizing redex → carrierCandidate redex) :
    HeadExpansionClosed (eitherProjectionMembersRight carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  exact eitherProjectionMembersRight_memberWeakHeadExpansion carrierHeadExpand
    WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN
      (scrutinee_isStronglyNormalizing_of_eitherProjectRight
        (carrierStronglyNormalizing contractumMember)))
    contractumMember

/-- **The option projection clause is congruent in its carrier.**  Pointwise-equivalent carriers yield
pointwise-equivalent option projection clauses — the clause is `carrierCandidate (optionProject term)`, so the
congruence is just the carrier equivalence read at `optionProject term`.  The determinism finisher the conjoined
option candidate's `_congr` consumes. -/
theorem optionProjectionMembers_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (optionProjectionMembers carrierCandidate1) (optionProjectionMembers carrierCandidate2) := by
  intro term
  exact carrierIff (optionProject term)

/-- **The either (inl) projection clause is congruent in its carrier.**  The Either twin of
`optionProjectionMembers_congr` — the carrier equivalence read at `eitherProject term`. -/
theorem eitherProjectionMembers_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (eitherProjectionMembers carrierCandidate1) (eitherProjectionMembers carrierCandidate2) := by
  intro term
  exact carrierIff (eitherProject term)

/-- **The either RIGHT (inr) projection clause is congruent in its carrier.**  The inr twin — the carrier
equivalence read at `eitherProjectRight term`. -/
theorem eitherProjectionMembersRight_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (eitherProjectionMembersRight carrierCandidate1)
      (eitherProjectionMembersRight carrierCandidate2) := by
  intro term
  exact carrierIff (eitherProjectRight term)

end FX1Poly.Core
