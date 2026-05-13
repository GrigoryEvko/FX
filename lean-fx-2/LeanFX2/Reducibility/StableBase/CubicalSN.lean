import LeanFX2.Reducibility.StableBase.LamFundamentals

/-! # LeanFX2.Reducibility.StableBase.CubicalSN

K12.24.U5 cubical SN preservation for the path / transport /
hcomp ctors: `RawTerm.pathApp_pathLam`,
`RawTerm.transp_pathLam_weaken`, `RawTerm.transp`, `RawTerm.hcomp`
plus their Term wrappers.

## Root status

Layer 3 metatheory leaf.  Third slice of K12.20.U4 stable base. -/

namespace LeanFX2


/-- **K12.24.U5 path β SN expansion**.

If the path body, interval argument, and β-contractum are all strongly
normalizing, then the cubical redex `pathApp (pathLam body) interval`
is strongly normalizing.  This mirrors `app_lam_isStronglyNormalizing`:
congruence reducts recurse through the body/interval SN witnesses, while
the β arm is closed by CR2 from the contractum along `subst0_par`. -/
theorem RawTerm.pathApp_pathLam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    ∀ {interval : RawTerm scope},
      RawTerm.isStronglyNormalizing interval →
      RawTerm.isStronglyNormalizing (body.subst0 interval) →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp (RawTerm.pathLam body) interval) := by
  induction bodyIsSN with
  | intro currentBody bodyClosure bodyIH =>
    intro interval intervalIsSN betaContractumIsSN
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp (RawTerm.pathLam currentBody) currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq,
          pathStep, intervalStep⟩
        | ⟨bodyTarget, intervalTarget, targetEq,
            pathStep, intervalStep⟩
      · obtain ⟨bodyTarget, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        subst pathTargetEq
        subst targetEq
        by_cases bodyEq : currentBody = bodyTarget
        · subst bodyEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact False.elim (progressStep.2 rfl)
          · have intervalContractumIsSN :
                RawTerm.isStronglyNormalizing
                  (currentBody.subst0 intervalTarget) := by
              by_cases contractumEq :
                  currentBody.subst0 currentInterval =
                    currentBody.subst0 intervalTarget
              · rw [← contractumEq]
                exact betaContractumIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  betaContractumIsSN
                  ⟨RawStep.par.subst0_par (RawStep.par.refl currentBody)
                    intervalStep, contractumEq⟩
            exact intervalIH intervalTarget ⟨intervalStep, intervalEq⟩
              intervalContractumIsSN
        · have bodyProgress :
              RawStep.parProgress currentBody bodyTarget :=
            ⟨bodyStep, bodyEq⟩
          have intervalTargetIsSN :
              RawTerm.isStronglyNormalizing intervalTarget := by
            by_cases intervalEq : currentInterval = intervalTarget
            · subst intervalEq
              exact RawTerm.isStronglyNormalizing.intro
                currentInterval intervalClosure
            · exact intervalClosure intervalTarget
                ⟨intervalStep, intervalEq⟩
          have bodyTargetContractumIsSN :
              RawTerm.isStronglyNormalizing
                (bodyTarget.subst0 intervalTarget) := by
            by_cases contractumEq :
                currentBody.subst0 currentInterval =
                  bodyTarget.subst0 intervalTarget
            · rw [← contractumEq]
              exact betaContractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                betaContractumIsSN
                ⟨RawStep.par.subst0_par bodyStep intervalStep,
                  contractumEq⟩
          exact bodyIH bodyTarget bodyProgress intervalTargetIsSN
            bodyTargetContractumIsSN
      · obtain ⟨bodyTargetFromPath, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq
        subst targetEq
        by_cases contractumEq :
            currentBody.subst0 currentInterval =
              bodyTarget.subst0 intervalTarget
        · rw [← contractumEq]
          exact betaContractumIsSN
        · exact RawTerm.isStronglyNormalizing.step_preserves
            betaContractumIsSN
            ⟨RawStep.par.subst0_par bodyStep intervalStep, contractumEq⟩

/-- Typed wrapper for cubical path β SN expansion.

The theorem only exposes the SN bridge for
`pathApp (pathLam body) interval`; Reducible-level backward closure at
the carrier type remains a separate head-β/CR3 problem. -/
theorem Term.pathApp_pathLam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {intervalRaw : RawTerm scope}
    {bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm)
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing (Term.subst0 bodyTerm intervalTerm)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTerm)
        intervalTerm) :=
  RawTerm.pathApp_pathLam_isStronglyNormalizing bodyIsSN intervalIsSN
    contractumIsSN

/-- **K12.24.U5 constant transport beta SN expansion**.

Transport across a syntactically constant path is strongly normalizing
whenever the transported value is.  Congruence on the constant path body
recurses through `RawStep.par.weaken_inv`; beta branches return a reduct
of the transported source.  The unrelated `uaToEquiv` and `pathCompose`
transport rules are impossible from a `pathLam _` head. -/
theorem RawTerm.transp_pathLam_weaken_isStronglyNormalizing {scope : Nat}
    {typeRaw : RawTerm scope}
    (typeIsSN : RawTerm.isStronglyNormalizing typeRaw) :
    ∀ {sourceRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing sourceRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw) := by
  induction typeIsSN with
  | intro currentType typeClosure typeIH =>
    intro sourceRaw sourceIsSN
    induction sourceIsSN with
    | intro currentSource sourceClosure sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.transp (RawTerm.pathLam currentType.weaken)
          currentSource) ?_
      intro target progressStep
      rcases RawStep.par.transp_inv progressStep.1 with
        ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨typeRawSource, sourceTarget, pathEq, targetEq, sourceStep⟩
        | ⟨typeRawTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨proofRawSource, proofRawTarget, sourceTarget,
            pathEq, targetEq, _proofStep, _sourceStep⟩
        | ⟨proofRawTarget, sourceTarget, targetEq, pathStep, _sourceStep⟩
        | ⟨leftRawSource, leftRawTarget, rightRawSource, rightRawTarget,
            sourceTarget, pathEq, targetEq, _leftStep, _rightStep,
            _sourceStep⟩
        | ⟨leftRawTarget, rightRawTarget, sourceTarget, targetEq,
            pathStep, _sourceStep⟩
      · obtain ⟨bodyTarget, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        subst pathTargetEq
        subst targetEq
        obtain ⟨typeTarget, bodyTargetEq⟩ :=
          RawStep.par.weaken_inv bodyStep
        subst bodyTargetEq
        have typeStep : RawStep.par currentType typeTarget := by
          have singletonStep :
              RawStep.par
                (currentType.weaken.subst
                  (RawTermSubst.singleton RawTerm.unit))
                (typeTarget.weaken.subst
                  (RawTermSubst.singleton RawTerm.unit)) :=
            RawStep.par.subst_par
              (fun _position => RawStep.par.refl _) bodyStep
          rw [RawTerm.weaken_subst_singleton currentType RawTerm.unit,
              RawTerm.weaken_subst_singleton typeTarget RawTerm.unit]
            at singletonStep
          exact singletonStep
        by_cases typeEq : currentType = typeTarget
        · subst typeEq
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact False.elim (progressStep.2 rfl)
          · exact sourceIH sourceTarget ⟨sourceStep, sourceEq⟩
        · have sourceTargetIsSN :
              RawTerm.isStronglyNormalizing sourceTarget := by
            by_cases sourceEq : currentSource = sourceTarget
            · subst sourceEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSource sourceClosure
            · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
          exact typeIH typeTarget ⟨typeStep, typeEq⟩ sourceTargetIsSN
      · rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · cases pathEq
      · obtain ⟨bodyTarget, pathTargetEq, _bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq
      · cases pathEq
      · obtain ⟨bodyTarget, pathTargetEq, _bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq

/-- Typed wrapper for constant cubical-transport beta SN expansion.

This packages the raw fact for the typed redex
`transp (pathLam typeCode.weaken) sourceValue`.  It is an SN bridge
only: no full transport Reducible endpoint is claimed here. -/
theorem Term.transp_pathLam_weaken_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType : Ty level scope}
    {typeRaw sourceRaw : RawTerm scope}
    {typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (typeCodeIsSN : Term.isStronglyNormalizing typeCode)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType sourceType typeRaw typeRaw
        (Term.pathLam modeIsUnivalent
          (Ty.universe universeLevel universeLevelLt) typeRaw typeRaw
          (Term.weaken Ty.interval typeCode))
        sourceValue) :=
  RawTerm.transp_pathLam_weaken_isStronglyNormalizing typeCodeIsSN
    sourceIsSN

/-- General raw transport SN bridge with explicit non-congruence obligations.

`transp` is not a congruence-only constructor: `transp_inv` has direct
and deep beta arms for constant paths, univalence paths, and composed
paths.  The constant-path arms reduce to a reduct of the source term,
which follows from `sourceIsSN`.  The univalence and compose contracta
are not derivable from child SN alone here, so callers must provide the
two explicit contractum-SN closures. -/
theorem RawTerm.transp_isStronglyNormalizing {scope : Nat}
    {pathRaw : RawTerm scope}
    (pathIsSN : RawTerm.isStronglyNormalizing pathRaw) :
    ∀ {sourceRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing sourceRaw →
      (∀ {currentPath currentSource proofTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath (RawTerm.uaToEquiv proofTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply (RawTerm.uaToEquiv proofTarget)
            sourceTarget)) →
      (∀ {currentPath currentSource leftTarget rightTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath
          (RawTerm.pathCompose leftTarget rightTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightTarget
            (RawTerm.transp leftTarget sourceTarget))) →
      RawTerm.isStronglyNormalizing (RawTerm.transp pathRaw sourceRaw) := by
  induction pathIsSN with
  | intro currentPath pathClosure pathIH =>
    intro sourceRaw sourceIsSN uaContractumIsSN composeContractumIsSN
    induction sourceIsSN with
    | intro currentSource sourceClosure sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.transp currentPath currentSource) ?_
      intro target progressStep
      let sourceTargetIsSN
          {sourceTarget : RawTerm scope}
          (sourceStep : RawStep.par currentSource sourceTarget) :
          RawTerm.isStronglyNormalizing sourceTarget := by
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      rcases RawStep.par.transp_inv progressStep.1 with
        ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨_typeRawSource, sourceTarget, _pathEq,
            targetEq, sourceStep⟩
        | ⟨_typeRawTarget, sourceTarget, targetEq,
            _pathStep, sourceStep⟩
        | ⟨_proofRawSource, proofRawTarget, sourceTarget,
            pathEq, targetEq, proofStep, sourceStep⟩
        | ⟨proofRawTarget, sourceTarget, targetEq,
            pathStep, sourceStep⟩
        | ⟨leftRawSource, leftRawTarget, rightRawSource,
            rightRawTarget, sourceTarget, pathEq, targetEq,
            leftStep, rightStep, sourceStep⟩
        | ⟨leftRawTarget, rightRawTarget, sourceTarget,
            targetEq, pathStep, sourceStep⟩
      · subst targetEq
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact False.elim (progressStep.2 rfl)
          · exact sourceIH sourceTarget ⟨sourceStep, sourceEq⟩
        · exact pathIH pathTarget ⟨pathStep, pathEq⟩
            (sourceTargetIsSN sourceStep)
            uaContractumIsSN composeContractumIsSN
      · rw [targetEq]
        exact sourceTargetIsSN sourceStep
      · rw [targetEq]
        exact sourceTargetIsSN sourceStep
      · subst targetEq
        subst pathEq
        exact uaContractumIsSN
          (RawStep.par.uaToEquivCong proofStep) sourceStep
      · rw [targetEq]
        exact uaContractumIsSN pathStep sourceStep
      · subst targetEq
        subst pathEq
        exact composeContractumIsSN
          (RawStep.par.pathComposeCong leftStep rightStep) sourceStep
      · rw [targetEq]
        exact composeContractumIsSN pathStep sourceStep

/-- Typed transport SN endpoint with the raw beta-contractum obligations
kept visible.

This is the honest surface endpoint for `Term.transp`: child SN proves
the congruence and constant-path beta branches, while univalence and
path-composition beta branches are explicit premises until their typed
contractum closures are integrated into the relevant reducibility cases. -/
theorem Term.transp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIsSN : Term.isStronglyNormalizing typePath)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue)
    (uaContractumIsSN :
      ∀ {currentPath currentSource proofTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath (RawTerm.uaToEquiv proofTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply (RawTerm.uaToEquiv proofTarget)
            sourceTarget))
    (composeContractumIsSN :
      ∀ {currentPath currentSource leftTarget rightTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath
          (RawTerm.pathCompose leftTarget rightTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightTarget
            (RawTerm.transp leftTarget sourceTarget))) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) :=
  RawTerm.transp_isStronglyNormalizing pathIsSN sourceIsSN
    uaContractumIsSN composeContractumIsSN

/-- **K12.24 hcomp SN preservation**.

The current raw `hcomp` operator has congruence only: all progress
steps are pointwise steps in the sides and cap payloads.  Therefore SN
of both payloads gives SN of the `hcomp` term by the same nested
induction pattern as binary constructors.  This is not a boundary
computation rule and does not claim full Reducible output at an
arbitrary carrier. -/
theorem RawTerm.hcomp_isStronglyNormalizing {scope : Nat}
    {sidesRaw : RawTerm scope}
    (sidesIsSN : RawTerm.isStronglyNormalizing sidesRaw) :
    ∀ {capRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing capRaw →
      RawTerm.isStronglyNormalizing (RawTerm.hcomp sidesRaw capRaw) := by
  induction sidesIsSN with
  | intro currentSides sidesClosure sidesIH =>
    intro capRaw capIsSN
    induction capIsSN with
    | intro currentCap capClosure capIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.hcomp currentSides currentCap) ?_
      intro target progressStep
      obtain ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ :=
        RawStep.par.hcomp_inv progressStep.1
      subst targetEq
      by_cases sidesEq : currentSides = sidesTarget
      · subst sidesEq
        by_cases capEq : currentCap = capTarget
        · subst capEq
          exact False.elim (progressStep.2 rfl)
        · exact capIH capTarget ⟨capStep, capEq⟩
      · have sidesProgress :
            RawStep.parProgress currentSides sidesTarget :=
          ⟨sidesStep, sidesEq⟩
        have capTargetIsSN : RawTerm.isStronglyNormalizing capTarget := by
          by_cases capEq : currentCap = capTarget
          · subst capEq
            exact RawTerm.isStronglyNormalizing.intro currentCap capClosure
          · exact capClosure capTarget ⟨capStep, capEq⟩
        exact sidesIH sidesTarget sidesProgress capTargetIsSN

/-- Typed wrapper for homogeneous-composition SN preservation.

This mirrors the raw congruence-only `hcomp` fragment.  It supplies the
SN bridge needed for cubical support work while keeping the Reducible
carrier closure separate. -/
theorem Term.hcomp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIsSN : Term.isStronglyNormalizing sidesValue)
    (capIsSN : Term.isStronglyNormalizing capValue) :
    Term.isStronglyNormalizing
      (Term.hcomp modeIsUnivalent sidesValue capValue) :=
  RawTerm.hcomp_isStronglyNormalizing sidesIsSN capIsSN


end LeanFX2
