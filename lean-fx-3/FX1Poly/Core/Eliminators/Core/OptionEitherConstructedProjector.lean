import FX1Poly.Core.Metatheory.Canonicity.OptionEitherMatchCanonicalComputation

/-! # FX1Poly/Core/OptionEitherConstructedProjector
    — the constructed eliminator-as-projector for option/either (the #1755 option/either residue foundation)

The native `fst` / `snd` projection eliminators let the product reducibility clause
(`sigmaProjectionMembers`) read a component's membership off the projection by FORWARD closure:
`carrierCandidate (fstCell scrutinee)` carries to `carrierCandidate first` along
`fstCell scrutinee ↠ fstCell (pairCell first second) ↝ first`.  Option/either have NO built-in
projection eliminator (no `unsome` / `uninl`), so the same trick has no off-the-shelf projector.

This file CONSTRUCTS the missing projector from the existing match eliminator + an identity branch:

  * `optionProject s := optionMatch dummyMotive dummyNone (lam dummyAnn (var 0)) s` — the some-branch is the
    identity lambda, the motive / none-branch are fixed CLOSED NORMAL dummies (`optionNone`), so the only
    non-normal child is the scrutinee.  When the scrutinee is `optionSome value`, the some-ι fires to
    `app (lam dummyAnn (var 0)) value`, which β-reduces to `subst0 (var 0) value = value` — so `optionProject`
    PROJECTS the payload exactly as `fst` projects a pair's first component.
  * `eitherProject` — the symmetric construction over the inl-ι (it projects an `eitherInl value`'s payload).

The headline forward-projection lemmas `optionProject_forwardToPayload` / `eitherProject_forwardToInlPayload`
are the option/either analogues of `StepStar.transLast (StepStar.fstScrutinee …) iotaFstPair.toStep`: a member
reaching `optionSome value` / `eitherInl value` drives `optionProject` / `eitherProject` to `value` by the
scrutinee-congruence chain then the ι+β.  The reducibility clause built on top of these (a later brick) then
carries `carrierCandidate (optionProject s)` forward to `carrierCandidate value` — discharging the
`someBranchMemberIfReachesSome` / `leftBranchMemberIfReachesInl` reach-residues at ARBITRARY (non-normal)
payloads, exactly as `sigmaProjectionMembers_firstComponentOfReachesPair` does for `fst`.

## Zero-axiom verification

The projectors are plain `mkGen` term-formers; the reductions chain the shipped scrutinee-congruence
(`StepStar.optionMatchScrutinee`), the some/inl ι (`IotaHeadStep.iotaOptionMatchSome` / `iotaEitherMatchInl`),
and β (`Step.beta`), with the identity-branch contraction `subst0 (var 0) value = value` holding by
`RawTerm.subst0_var_zero` (definitional).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open StepStar

/-- A fixed closed normal dummy term — `optionNone`, a nullary value available at every scope, used for the
projector's discarded motive / none-branch / domain annotation.  `abbrev` so the eliminator reductions'
implicit motive/branch arguments resolve by unfolding. -/
abbrev projectorDummy {scope : Nat} : RawTerm scope :=
  .mkGen .gen_optionNone () .childNil

/-- The identity lambda `lam projectorDummy (var 0)` — the projector's some/inl branch.  Applying it to a
payload β-reduces to the payload (`subst0 (var 0) value = value`). -/
abbrev projectorIdentityBranch {scope : Nat} : RawTerm scope :=
  .mkGen .gen_lam ()
    (.childCons projectorDummy
      (.childCons (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) .childNil))

/-- **The constructed option projector.**  `optionMatch` whose some-branch is the identity lambda and whose
motive / none-branch are fixed normal dummies — projects an `optionSome value`'s payload. -/
abbrev optionProject {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons projectorDummy
      (.childCons projectorDummy
        (.childCons projectorIdentityBranch (.childCons scrutinee .childNil))))

/-- **The constructed either projector.**  `eitherMatch` whose left-branch is the identity lambda and whose
motive / right-branch are fixed normal dummies — projects an `eitherInl value`'s payload. -/
abbrev eitherProject {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons projectorDummy
      (.childCons projectorIdentityBranch
        (.childCons projectorDummy (.childCons scrutinee .childNil))))

/-- **The constructed either RIGHT projector.**  `eitherMatch` whose RIGHT-branch is the identity lambda and
whose motive / left-branch are fixed normal dummies — projects an `eitherInr value`'s payload.  The inr twin of
`eitherProject`: where `eitherProject` reads off the inl payload (carrier `firstCandidate`), this reads off the
inr payload (carrier `secondCandidate`), so the two together resolve BOTH reach residues of the native
`eitherMatch` elim FT row. -/
abbrev eitherProjectRight {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons projectorDummy
      (.childCons projectorDummy
        (.childCons projectorIdentityBranch (.childCons scrutinee .childNil))))

/-- **The identity branch applied to a payload β-reduces to the payload.**  `app (lam dummy (var 0)) value ↝
subst0 (var 0) value`, and `subst0 (var 0) value = value` definitionally (`RawTerm.subst0_var_zero`). -/
theorem projectorIdentityBranch_app_reducesToPayload {scope : Nat} (value : RawTerm scope) :
    Step (.mkGen .gen_app () (.childCons projectorIdentityBranch (.childCons value .childNil))) value := by
  have betaStep :
      Step (.mkGen .gen_app () (.childCons projectorIdentityBranch (.childCons value .childNil)))
        (RawTerm.subst0 (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) value) := Step.beta
  rwa [RawTerm.subst0_var_zero] at betaStep

/-- **`optionProject (optionSome value)` reduces to `value`.**  The some-ι fires the identity branch
(`IotaHeadStep.iotaOptionMatchSome`), and `app (identity branch) value` β-reduces to `value`. -/
theorem optionProject_someCell_reducesToPayload {scope : Nat} (value : RawTerm scope) :
    StepStar (optionProject (.mkGen .gen_optionSome () (.childCons value .childNil))) value :=
  StepStar.trans
    (IotaHeadStep.iotaOptionMatchSome (motive := projectorDummy)
      (noneBranch := projectorDummy) (someBranch := projectorIdentityBranch)).toStep
    (StepStar.single (projectorIdentityBranch_app_reducesToPayload value))

/-- **`eitherProject (eitherInl value)` reduces to `value`.**  Symmetric to the option case over the inl-ι
(`IotaHeadStep.iotaEitherMatchInl`). -/
theorem eitherProject_inlCell_reducesToPayload {scope : Nat} (value : RawTerm scope) :
    StepStar (eitherProject (.mkGen .gen_eitherInl () (.childCons value .childNil))) value :=
  StepStar.trans
    (IotaHeadStep.iotaEitherMatchInl (motive := projectorDummy)
      (leftBranch := projectorIdentityBranch) (rightBranch := projectorDummy)).toStep
    (StepStar.single (projectorIdentityBranch_app_reducesToPayload value))

/-- **`eitherProjectRight (eitherInr value)` reduces to `value`.**  The inr twin: the inr-ι
(`IotaHeadStep.iotaEitherMatchInr`) fires the right (identity) branch, and `app (identity branch) value`
β-reduces to `value`. -/
theorem eitherProjectRight_inrCell_reducesToPayload {scope : Nat} (value : RawTerm scope) :
    StepStar (eitherProjectRight (.mkGen .gen_eitherInr () (.childCons value .childNil))) value :=
  StepStar.trans
    (IotaHeadStep.iotaEitherMatchInr (motive := projectorDummy)
      (leftBranch := projectorDummy) (rightBranch := projectorIdentityBranch)).toStep
    (StepStar.single (projectorIdentityBranch_app_reducesToPayload value))

/-- **★ Forward projection: a scrutinee reaching `optionSome value` drives `optionProject` to `value`.**  The
scrutinee-congruence chain (`StepStar.optionMatchScrutinee`) carries the reach under the `optionMatch`, then
the some-ι + β contract the identity branch.  The option analogue of `StepStar.transLast (StepStar.fstScrutinee
…) iotaFstPair.toStep` — the forward-closure driver the option reducibility clause's reach-residue resolver
consumes (`someBranchMemberIfReachesSome` at an ARBITRARY, possibly non-normal, payload). -/
theorem optionProject_forwardToPayload {scope : Nat} {scrutinee value : RawTerm scope}
    (reachesSome : StepStar scrutinee (.mkGen .gen_optionSome () (.childCons value .childNil))) :
    StepStar (optionProject scrutinee) value :=
  StepStar.trans_compose (StepStar.optionMatchScrutinee reachesSome)
    (optionProject_someCell_reducesToPayload value)

/-- **★ Forward projection: a scrutinee reaching `eitherInl value` drives `eitherProject` to `value`.**
Symmetric to `optionProject_forwardToPayload` over the inl-ι — the either reach-residue resolver's driver
(`leftBranchMemberIfReachesInl`). -/
theorem eitherProject_forwardToInlPayload {scope : Nat} {scrutinee value : RawTerm scope}
    (reachesInl : StepStar scrutinee (.mkGen .gen_eitherInl () (.childCons value .childNil))) :
    StepStar (eitherProject scrutinee) value :=
  StepStar.trans_compose (StepStar.eitherMatchScrutinee reachesInl)
    (eitherProject_inlCell_reducesToPayload value)

/-- **★ Forward projection: a scrutinee reaching `eitherInr value` drives `eitherProjectRight` to `value`.**
The inr twin of `eitherProject_forwardToInlPayload` — the driver the either reach-residue resolver's RIGHT side
(`rightBranchMemberIfReachesInr`) consumes at an ARBITRARY (possibly non-normal) payload. -/
theorem eitherProjectRight_forwardToInrPayload {scope : Nat} {scrutinee value : RawTerm scope}
    (reachesInr : StepStar scrutinee (.mkGen .gen_eitherInr () (.childCons value .childNil))) :
    StepStar (eitherProjectRight scrutinee) value :=
  StepStar.trans_compose (StepStar.eitherMatchScrutinee reachesInr)
    (eitherProjectRight_inrCell_reducesToPayload value)

end FX1Poly.Core
