import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranches
import FX1Poly.Typed.Metatheory.SubjectReduction.StepStarCellCongruence

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateDispatch
    — SR-DSL-5: inhabiting the introducer-congruence gate by dispatch over the intro table

`IntroGateBranches.lean` ships the per-generator branch lemmas for SIXTEEN of the seventeen introducer rows
(the eight nullary data constructors, the six recursive/grown data constructors, `refl`, and `lam`); the
seventeenth, `pathLam`, is blocked by the interval-fibrancy obstruction (the staged interval-non-fibrant arc).
This file CLOSES the gate `UnionIntroCongruenceCloses` MODULO exactly that one honest blocker: it takes the
`pathLam` branch as a single explicit premise (`PathLamIntroGateBranchCloses`) and dispatches all seventeen rows
of `introRuleOf_cases` to their branch lemmas — the sixteen shipped ones directly, the `pathLam` row to the
premise.

So the entire INTRODUCER leg of the native congruence mountain (`UnionIntroCongruenceCloses`, one of the three
gates `HasTypeUnion.unionCongruenceCloserOfGates` reduces the congruence closer to) now rests on the ONE
`pathLam` branch the A1 / interval-non-fibrant lineage discharges; nothing else in the intro arm remains open.
The dispatch follows the row ORDER of `introRuleOf_cases` (not the source order of the branch file).

## Zero-axiom

`introRuleOf_cases` (the `by_cases` table enumerator) + the sixteen shipped branch lemmas + the supplied
`pathLam` branch.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The `pathLam` introducer-congruence branch, isolated as a premise.**  The seventeenth introducer row's
closure obligation on its own: when a `pathLam` cell `pathLamIntroRule.memberCell scope args` (typed at its
`outputType`) is a `.mkGen` whose children step, the reformed cell re-types at a `Conv`-equal classifier.
Mirrors the shipped `lamIntroGateBranchCloses` shape at `pathLamIntroRule`; the A1 / interval-non-fibrant
lineage discharges it, at which point the intro gate becomes unconditional. -/
def PathLamIntroGateBranchCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pathLamIntroRule.argShifts scope)
    (params : RawTermChildren pathLamIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    pathLamIntroRule.sideCondition scope args →
    (∀ obligation ∈ pathLamIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ pathLamIntroRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    UnionChildSubjectReduction profile →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      pathLamIntroRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (pathLamIntroRule.outputType scope args params)

/-- **★ The introducer-congruence gate, modulo the `pathLam` branch.**  Given the one `pathLam` branch, the
gate `UnionIntroCongruenceCloses` holds: dispatch `introRuleOf_cases` over all seventeen rows — the sixteen
shipped branch lemmas for the data constructors + `lam`, and the supplied premise for `pathLam`.  The whole
intro leg of the native congruence mountain is now this single honest obligation. -/
theorem HasTypeUnion.unionIntroCongruenceClosesOfPathLam {profile : PolyProfile}
    (pathLamBranch : PathLamIntroGateBranchCloses profile) :
    UnionIntroCongruenceCloses profile := by
  intro scope context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
    usabilityHolds childSubjectReduction wellFormed reformedGenerator reformedPayload childrenBefore
    childrenAfter memberEq childStep
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact boolTrueIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact boolFalseIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact unitIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact interval0IntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact interval1IntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact natZeroIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact lamIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact pathLamBranch args params level0 level1 flag sideHolds premisesHold
      usabilityHolds childSubjectReduction wellFormed memberEq childStep
  · exact natSuccIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact listConsIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact optionSomeIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact optionNoneIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact listNilIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact eitherInlIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact eitherInrIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact pairIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep
  · exact reflIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed usabilityHolds memberEq childStep

/-! ## ★ Discharging the `pathLam` branch — the BETA-STABLE App-scaled side condition

After the side-condition swap (`pathLamIntroRule.sideCondition` = the App-SCALED affine grade `appScaled body 0
≤ one`, NOT the beta-FRAGILE raw occurrence count), the `pathLam` branch's residual obligation is to re-establish
that grade on the STEPPED body — which is exactly AFFINE SUBJECT REDUCTION.  This holds in the TYPED setting
(typing forces every inner `pathLam` affine, so no inner endpoint-β can duplicate the dimension), but is FALSE as
a raw-term lemma — a raw body admits a non-affine inner `pathLam` whose endpoint-β blows the grade to `omega`.
So the discharge is CONDITIONAL on one honest believed-true Prop `PathLamBodyStepPreservesAppScaledAffine`,
committed in the spirit of `IsAppScaledSubst0Bounded` (a believed-true Prop committed before its discharge).
The output drift (`bridge`-code endpoint congruence under the body's `subst0`-endpoint reductions) and the
obligation drift are UNCONDITIONAL. -/

/-- **The honest affine-subject-reduction Prop the `pathLam` branch rests on** (believed-true,
mechanically-grindable via the affine-substitution-equivariance metatheory + inner-`pathLam` affineness
inversion — task A1-SUBST-OPEN).  When a TYPED body steps, its BETA-STABLE App-scaled freshest-binder affine
grade is preserved.  TRUE because typing forces every inner `pathLam` affine; NOT a raw-term lemma (a raw body
admits a non-affine inner `pathLam` whose endpoint-β duplicates the dimension), which is exactly why it is
isolated here rather than discharged.  The single residual SR-arc `pathLam` obligation after the swap. -/
def PathLamBodyStepPreservesAppScaledAffine (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile (scope + 1)}
    {body body' classifier : RawTerm (scope + 1)},
    HasTypeUnion profile context body classifier →
    Step body body' →
    UsageGrade.le (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one = true →
    UsageGrade.le (RawTerm.appScaledDimensionGrade body' ⟨0, Nat.succ_pos scope⟩) UsageGrade.one = true

/-- Replay a `StepStar` chain in the LEFT endpoint of a `bridgeTypeCell` (type code + right endpoint fixed):
each head step lifted by `Step.cong gen_bridgeCode` at the second child position. -/
theorem StepStar.bridgeLeftStar {scope : Nat} (typeCode : RawTerm scope)
    {leftStart leftTarget : RawTerm scope} (right : RawTerm scope)
    (chain : StepStar leftStart leftTarget) :
    StepStar (bridgeTypeCell typeCode leftStart right) (bridgeTypeCell typeCode leftTarget right) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _ tailReduces =>
      exact StepStar.trans
        (Step.cong .gen_bridgeCode () (.there _ (.here _ headStep)))
        tailReduces

/-- Replay a `StepStar` chain in the RIGHT endpoint of a `bridgeTypeCell` (type code + left endpoint fixed):
each head step lifted by `Step.cong gen_bridgeCode` at the third child position. -/
theorem StepStar.bridgeRightStar {scope : Nat} (typeCode left : RawTerm scope)
    {rightStart rightTarget : RawTerm scope}
    (chain : StepStar rightStart rightTarget) :
    StepStar (bridgeTypeCell typeCode left rightStart) (bridgeTypeCell typeCode left rightTarget) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _ tailReduces =>
      exact StepStar.trans
        (Step.cong .gen_bridgeCode () (.there _ (.there _ (.here _ headStep))))
        tailReduces

/-- **★ The `pathLam` introducer-congruence branch, MODULO `PathLamBodyStepPreservesAppScaledAffine`.**  The
seventeenth introducer row's closure: the body obligation drifts (`StepStar.single bodyStep`, the
interval-locked context fixed) and the `bridge`-code output drifts at BOTH endpoints (the body's
`subst0`-endpoint reductions, via `bridgeLeftStar`/`bridgeRightStar`); the re-established side condition
`sideHoldsAfter` is the App-scaled affine grade transported across the body step by the conditional Prop.
Mirrors `lamIntroGateBranchCloses` at `pathLamIntroRule`.  Discharging `PathLamBodyStepPreservesAppScaledAffine`
makes the whole intro gate — and the native congruence mountain — unconditional. -/
theorem pathLamIntroGateBranchCloses {profile : PolyProfile}
    (bodyStepPreservesAffine : PathLamBodyStepPreservesAppScaledAffine profile) :
    PathLamIntroGateBranchCloses profile := by
  intro scope context args params level0 level1 flag sideHolds premisesHold usabilityHolds
    childSubjectReduction wellFormed reformedGenerator reformedPayload childrenBefore childrenAfter
    memberEq childStep
  match args, params with
  | .childCons body .childNil, .childCons carrierCode .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have bodyTyped : HasTypeUnion profile (context.lockCons intervalTypeCell) body
        (RawTerm.weaken carrierCode) :=
      premisesHold _ (List.Mem.head _)
    have intervalWellFormed : WfContextUnion (context.lockCons intervalTypeCell) :=
      WfContextUnion.lockCons wellFormed rfl
    have classifierFormed : UnionClassifierIsType profile (context.lockCons intervalTypeCell)
        (RawTerm.weaken carrierCode) :=
      HasTypeUnion.classifierIsType bodyTyped intervalWellFormed
    cases childStep with
    | @here _ _ _ _ bodyPrime _ bodyStep =>
        -- ★ The ONLY conditional ingredient: the swapped App-scaled affine side condition is preserved
        -- across the body step by the honest affine-subject-reduction Prop.
        have sideHoldsAfter :
            pathLamIntroRule.sideCondition scope (.childCons bodyPrime .childNil) :=
          bodyStepPreservesAffine bodyTyped bodyStep sideHolds
        have driftAt : ObligationsDrift profile
            (pathLamIntroRule.obligations scope context (.childCons body .childNil)
              (.childCons carrierCode .childNil) level0 level1 flag)
            (pathLamIntroRule.obligations scope context (.childCons bodyPrime .childNil)
              (.childCons carrierCode .childNil) level0 level1 flag) :=
          .cons (StepStar.single bodyStep) (StepStar.refl _) classifierFormed .nil
        have outputDriftAt : Conv
            (pathLamIntroRule.outputType scope (.childCons bodyPrime .childNil)
              (.childCons carrierCode .childNil))
            (pathLamIntroRule.outputType scope (.childCons body .childNil)
              (.childCons carrierCode .childNil)) :=
          ⟨_, StepStar.refl _,
            StepStar.trans_compose
              (StepStar.bridgeLeftStar carrierCode (RawTerm.subst0 body intervalOneCell)
                (StepStar.subst0Body intervalZeroCell (StepStar.single bodyStep)))
              (StepStar.bridgeRightStar carrierCode (RawTerm.subst0 bodyPrime intervalZeroCell)
                (StepStar.subst0Body intervalOneCell (StepStar.single bodyStep)))⟩
        exact introGateRowReassemble (argsAfter := .childCons bodyPrime .childNil)
          .gen_pathLam pathLamIntroRule (.childCons carrierCode .childNil) level0 level1 flag
          introRuleOf_pathLam premisesHold childSubjectReduction sideHoldsAfter driftAt outputDriftAt
          (usabilityHoldsUnderObligationsDrift driftAt childSubjectReduction
            (by intro obligation memberProof; cases memberProof with
              | head => rfl
              | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
    | there _ tail => cases tail

end FX1Poly.Typed
