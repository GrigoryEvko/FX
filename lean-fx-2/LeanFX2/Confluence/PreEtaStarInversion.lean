import LeanFX2.Reduction.Conv
import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Confluence.RawParStarCong

/-! # PreEtaStarInversion — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # LeanFX2.Confluence.PreEtaStarInversion

Raw-projection inversion lemmas for binder-headed typed `Step.parStar`
sources.

These are multi-step counterparts to
`Reduction/ParRed/PreEtaInversion.lean`.  They deliberately stay at the
raw projection layer: a typed chain starting from a binder-headed source
projects to a raw chain whose target keeps the same binder head, and the
body projection is related by `RawStep.parStar`.

This is still pre-eta infrastructure.  The later T9/T10/T11 typed
destructors need an additional eta disjunct plus typed reconstruction.
-/

namespace LeanFX2

namespace Step.parStar

/-- Raw-projection inversion for a multi-step chain from a non-dependent
lambda source. -/
theorem lam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.lam_inv (Step.parStar.toRawBridge parallelChain)

/-- Raw-projection inversion for a multi-step chain from a dependent
lambda source. -/
theorem lamPi_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.lam_inv (Step.parStar.toRawBridge parallelChain)

/-- Raw-projection inversion for a multi-step chain from a path-lambda
source. -/
theorem pathLam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.pathLam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.pathLam_inv (Step.parStar.toRawBridge parallelChain)

/-- Known-target raw-body inversion for a multi-step chain between
non-dependent lambdas. -/
theorem lam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons domainType) codomainType.weaken bodyRawTarget}
    (parallelChain :
      Step.parStar
        (Term.lam (codomainType := codomainType) bodySource)
        (Term.lam (codomainType := codomainType) bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyChain⟩ :=
    Step.parStar.lam_targetRaw_inv_congr parallelChain
  cases targetEq
  exact bodyChain

/-- Known-target raw-body inversion for a multi-step chain between
dependent lambdas. -/
theorem lamPi_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {bodyTarget : Term (context.cons domainType) codomainType bodyRawTarget}
    (parallelChain :
      Step.parStar (Term.lamPi (domainType := domainType) bodySource)
        (Term.lamPi (domainType := domainType) bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyChain⟩ :=
    Step.parStar.lamPi_targetRaw_inv_congr parallelChain
  cases targetEq
  exact bodyChain

/-- Known-target raw-body inversion for a multi-step chain between
path lambdas. -/
theorem pathLam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (parallelChain :
      Step.parStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyChain⟩ :=
    Step.parStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
      leftEndpoint rightEndpoint parallelChain
  cases targetEq
  exact bodyChain

end Step.parStar

namespace StepStar

/-- `StepStar` raw-projection inversion for a non-dependent lambda source.

This is the Conv-facing closure of
`Step.parStar.lam_targetRaw_inv_congr`: first lift the ordinary
single-step chain to a parallel chain, then reuse the raw binder-head
projection. -/
theorem lam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lam_targetRaw_inv_congr chain.toParStar

/-- `StepStar` raw-projection inversion for a dependent lambda source. -/
theorem lamPi_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lamPi_targetRaw_inv_congr chain.toParStar

/-- `StepStar` raw-projection inversion for a path-lambda source. -/
theorem pathLam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.pathLam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
    leftEndpoint rightEndpoint chain.toParStar

/-- `StepStar` known-target raw-body inversion for non-dependent lambdas. -/
theorem lam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons domainType) codomainType.weaken bodyRawTarget}
    (chain :
      StepStar
        (Term.lam (codomainType := codomainType) bodySource)
        (Term.lam (codomainType := codomainType) bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lam_bodyRaw_inv_congr chain.toParStar

/-- `StepStar` known-target raw-body inversion for dependent lambdas. -/
theorem lamPi_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {bodyTarget : Term (context.cons domainType) codomainType bodyRawTarget}
    (chain :
      StepStar (Term.lamPi (domainType := domainType) bodySource)
        (Term.lamPi (domainType := domainType) bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lamPi_bodyRaw_inv_congr chain.toParStar

/-- `StepStar` known-target raw-body inversion for path lambdas. -/
theorem pathLam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (chain :
      StepStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyTarget)) :
    RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.pathLam_bodyRaw_inv_congr modeIsUnivalent carrierType
    leftEndpoint rightEndpoint chain.toParStar

end StepStar

namespace Conv

/-- If the left endpoint of a `Conv` witness is a non-dependent lambda,
the typed common reduct's raw projection is lambda-headed.

This is a raw/index corollary only: it keeps the existing typed midpoint
from `Conv` and exposes the body-level raw `parStar` chain produced by
the left convergence path. -/
theorem lam_left_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (convertibility :
      Conv
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawTarget : RawTerm (scope + 1)),
        commonRaw = RawTerm.lam bodyRawTarget ∧
        StepStar
          (Term.lam (codomainType := codomainType) bodySource)
          commonTerm ∧
        StepStar targetTerm commonTerm ∧
        RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawTarget, commonRawEq, bodyChain⟩ :=
    StepStar.lam_targetRaw_inv_congr leftChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawTarget, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- If the left endpoint of a `Conv` witness is a dependent lambda, the
typed common reduct's raw projection is lambda-headed. -/
theorem lamPi_left_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (convertibility :
      Conv (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawTarget : RawTerm (scope + 1)),
        commonRaw = RawTerm.lam bodyRawTarget ∧
        StepStar (Term.lamPi (domainType := domainType) bodySource)
          commonTerm ∧
        StepStar targetTerm commonTerm ∧
        RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawTarget, commonRawEq, bodyChain⟩ :=
    StepStar.lamPi_targetRaw_inv_congr leftChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawTarget, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- If the left endpoint of a `Conv` witness is a path lambda, the typed
common reduct's raw projection is path-lambda-headed. -/
theorem pathLam_left_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (convertibility :
      Conv
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawTarget : RawTerm (scope + 1)),
        commonRaw = RawTerm.pathLam bodyRawTarget ∧
        StepStar
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint bodySource)
          commonTerm ∧
        StepStar targetTerm commonTerm ∧
        RawStep.parStar bodyRawSource bodyRawTarget := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawTarget, commonRawEq, bodyChain⟩ :=
    StepStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
      leftEndpoint rightEndpoint leftChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawTarget, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- If the right endpoint of a `Conv` witness is a non-dependent lambda,
the typed common reduct's raw projection is lambda-headed. -/
theorem lam_right_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {domainType codomainType : Ty level scope}
    {bodyRawTarget : RawTerm (scope + 1)}
    {bodyTarget :
      Term (context.cons domainType) codomainType.weaken bodyRawTarget}
    (convertibility :
      Conv sourceTerm
        (Term.lam (codomainType := codomainType) bodyTarget)) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawCommon : RawTerm (scope + 1)),
        commonRaw = RawTerm.lam bodyRawCommon ∧
        StepStar sourceTerm commonTerm ∧
        StepStar
          (Term.lam (codomainType := codomainType) bodyTarget)
          commonTerm ∧
        RawStep.parStar bodyRawTarget bodyRawCommon := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawCommon, commonRawEq, bodyChain⟩ :=
    StepStar.lam_targetRaw_inv_congr rightChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawCommon, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- If the right endpoint of a `Conv` witness is a dependent lambda, the
typed common reduct's raw projection is lambda-headed. -/
theorem lamPi_right_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawTarget : RawTerm (scope + 1)}
    {bodyTarget : Term (context.cons domainType) codomainType bodyRawTarget}
    (convertibility :
      Conv sourceTerm
        (Term.lamPi (domainType := domainType) bodyTarget)) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawCommon : RawTerm (scope + 1)),
        commonRaw = RawTerm.lam bodyRawCommon ∧
        StepStar sourceTerm commonTerm ∧
        StepStar (Term.lamPi (domainType := domainType) bodyTarget)
          commonTerm ∧
        RawStep.parStar bodyRawTarget bodyRawCommon := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawCommon, commonRawEq, bodyChain⟩ :=
    StepStar.lamPi_targetRaw_inv_congr rightChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawCommon, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- If the right endpoint of a `Conv` witness is a path lambda, the typed
common reduct's raw projection is path-lambda-headed. -/
theorem pathLam_right_commonRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawTarget : RawTerm (scope + 1)}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (convertibility :
      Conv sourceTerm
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyTarget)) :
    ∃ (commonType : Ty level scope) (commonRaw : RawTerm scope)
      (commonTerm : Term context commonType commonRaw)
      (bodyRawCommon : RawTerm (scope + 1)),
        commonRaw = RawTerm.pathLam bodyRawCommon ∧
        StepStar sourceTerm commonTerm ∧
        StepStar
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint bodyTarget)
          commonTerm ∧
        RawStep.parStar bodyRawTarget bodyRawCommon := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨bodyRawCommon, commonRawEq, bodyChain⟩ :=
    StepStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
      leftEndpoint rightEndpoint rightChain
  exact ⟨commonType, commonRaw, commonTerm, bodyRawCommon, commonRawEq,
    leftChain, rightChain, bodyChain⟩

/-- Raw body common-reduct corollary for convertible non-dependent
lambdas. -/
theorem lam_bodyRaw_common_join
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {leftBodyRaw rightBodyRaw : RawTerm (scope + 1)}
    {leftBody :
      Term (context.cons domainType) codomainType.weaken leftBodyRaw}
    {rightBody :
      Term (context.cons domainType) codomainType.weaken rightBodyRaw}
    (convertibility :
      Conv
        (Term.lam (codomainType := codomainType) leftBody)
        (Term.lam (codomainType := codomainType) rightBody)) :
    ∃ commonBodyRaw,
      RawStep.parStar leftBodyRaw commonBodyRaw ∧
      RawStep.parStar rightBodyRaw commonBodyRaw := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨leftCommonBodyRaw, leftRawEq, leftBodyChain⟩ :=
    StepStar.lam_targetRaw_inv_congr leftChain
  obtain ⟨rightCommonBodyRaw, rightRawEq, rightBodyChain⟩ :=
    StepStar.lam_targetRaw_inv_congr rightChain
  cases leftRawEq
  cases rightRawEq
  exact ⟨leftCommonBodyRaw, leftBodyChain, rightBodyChain⟩

/-- Raw body common-reduct corollary for convertible dependent
lambdas. -/
theorem lamPi_bodyRaw_common_join
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {leftBodyRaw rightBodyRaw : RawTerm (scope + 1)}
    {leftBody : Term (context.cons domainType) codomainType leftBodyRaw}
    {rightBody : Term (context.cons domainType) codomainType rightBodyRaw}
    (convertibility :
      Conv
        (Term.lamPi (domainType := domainType) leftBody)
        (Term.lamPi (domainType := domainType) rightBody)) :
    ∃ commonBodyRaw,
      RawStep.parStar leftBodyRaw commonBodyRaw ∧
      RawStep.parStar rightBodyRaw commonBodyRaw := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨leftCommonBodyRaw, leftRawEq, leftBodyChain⟩ :=
    StepStar.lamPi_targetRaw_inv_congr leftChain
  obtain ⟨rightCommonBodyRaw, rightRawEq, rightBodyChain⟩ :=
    StepStar.lamPi_targetRaw_inv_congr rightChain
  cases leftRawEq
  cases rightRawEq
  exact ⟨leftCommonBodyRaw, leftBodyChain, rightBodyChain⟩

/-- Raw body common-reduct corollary for convertible path lambdas. -/
theorem pathLam_bodyRaw_common_join
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {leftBodyRaw rightBodyRaw : RawTerm (scope + 1)}
    {leftBody :
      Term (context.cons Ty.interval) carrierType.weaken leftBodyRaw}
    {rightBody :
      Term (context.cons Ty.interval) carrierType.weaken rightBodyRaw}
    (convertibility :
      Conv
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint leftBody)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint rightBody)) :
    ∃ commonBodyRaw,
      RawStep.parStar leftBodyRaw commonBodyRaw ∧
      RawStep.parStar rightBodyRaw commonBodyRaw := by
  obtain ⟨commonType, commonRaw, commonTerm, leftChain, rightChain⟩ :=
    convertibility
  obtain ⟨leftCommonBodyRaw, leftRawEq, leftBodyChain⟩ :=
    StepStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
      leftEndpoint rightEndpoint leftChain
  obtain ⟨rightCommonBodyRaw, rightRawEq, rightBodyChain⟩ :=
    StepStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
      leftEndpoint rightEndpoint rightChain
  cases leftRawEq
  cases rightRawEq
  exact ⟨leftCommonBodyRaw, leftBodyChain, rightBodyChain⟩

end Conv

end LeanFX2

-/
