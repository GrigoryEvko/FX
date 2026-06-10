import FX1Poly.Typed.PlateauPinnedReflection
import FX1Poly.Typed.PinnedReflectionFlagCoherent
import FX1Poly.Typed.HasTypeDescPiFormerCongruence

/-! # FX1Poly/Typed/LamReductResidualDischarge — ★ the flag-coherent piElim residual HOLDS
     (the λ-classifier pin, closed by T2 + E3 — the strengthening campaign's open core)

The pinned-reflection campaign's one open arm was the piElim residual: an in-image application's
OUTPUT pin says nothing about the FUNCTION's Π classifier, and when the function whnf-reduces to a
λ the classifier's CODOMAIN floats (the shipped plateau pin-extraction explicitly EXCLUDES λ
heads).  Two shipped walls fall together here:

  * **T2** (Church-style `gen_lam`): the λ carries its domain annotation as a syntactic child, and
    `piIntro`'s classifier domain IS that annotation — so an in-image λ's classifier DOMAIN is
    pinned definitionally (`renameEqLamCellInversion` drills the annotation through the renaming).
  * **E3** (`pinBaseValidAtCallerPair`): the codomain reflects by STRUCTURAL RECURSION into the
    λ's body premise — the body is normal (`lamNormal_bodyNormal`) and in-image, so the same pin
    extraction applies one binder deeper — and the recursive pin's ∃-flag validity re-types at the
    caller's exact `(level, flag)` through the flag-coherent condition, so
    `piFormationViaGenArm` reassembles the source Π at ONE shared flag.

## What ships

  * `normalClassifierPinnedFlagCoherent` — the λ-INCLUSIVE pin extraction: the classifier of ANY
    normal, in-image, grown-typed term is pinned (no non-λ exclusion).  The piIntro arm is the new
    mathematics; the other arms mirror the shipped `normalNonLambdaClassifierPinned` with the
    coherent condition threaded (projected to the plain condition where the shipped bricks want it).
  * `pinnedReflectionPiElimCoreFlagCoherent` — the pinned-function core over the flag-coherent
    motive (the IH calls receive the coherent condition; everything else is the shipped core).
  * `pinnedReflectionPiElimResidualFlagCoherentHolds` — ★ THE DISCHARGE: the FULL flag-coherent
    piElim residual holds.  With the λ-inclusive extraction no head split is needed: normalize the
    function (grown-wf open SN), keep the Π classifier across the chain (subject reduction), pin
    the NORMAL reduct's classifier whatever its head, and finish through the coherent core.
  * `pinnedReflectionPiElimLamReductResidualFlagCoherentHolds` — the named λ-reduct target, as the
    umbrella's corollary.

The plain-condition residual remains open (the codomain's flag negotiation genuinely consumes the
condition's shared-universe triples — that is what E1 added them for); the strengthening endpoint
(STR-9) enters through `ContextReflectsRenameFlagCoherent.ofWeakenCons`, which produces the
coherent condition directly, so the coherent form is the campaign-sufficient one.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The λ-INCLUSIVE pin extraction (flag-coherent)**: the classifier of a NORMAL, in-image,
grown-typed term is pinned — with NO non-λ exclusion.  Derivation-structural; the piIntro arm
(the historical float) pins the domain SYNTACTICALLY (T2: the annotation is a subject child, so
`renameEqLamCellInversion` exposes the source domain), reflects the domain's universe typing
through the guarded master at a strictly smaller bound, recurses into the BODY premise for the
codomain pin (the body is normal and in-image one binder deeper), re-types the recursive pin at
the caller's exact `(level, flag)` via `pinBaseValidAtCallerPair` (E3), and reassembles the
source Π at the shared flag via `piFormationViaGenArm`. -/
theorem normalClassifierPinnedFlagCoherent {profile : PolyProfile} {budget : Nat}
    (residualWithinBudget : ∀ {smallBound : Nat}, smallBound ≤ budget →
      PinnedReflectionPiElimResidualGuarded profile smallBound)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier)
    (subjectNormal : RawTerm.isStepNormalForm subject)
    (subjectSize : subject.size ≤ budget)
    (targetWellFormed : WfContextDescPi targetContext)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (rhoInjective : Function.Injective rho)
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (wellFormed : WfContextDescPi sourceContext)
    {sourceSubject : RawTerm sourceScope}
    (subjectInImage : subject = RawTerm.rename rho sourceSubject) :
    ∃ base : RawTerm sourceScope,
      Conv classifier (RawTerm.rename rho base) ∧
      IsTypeDescPi profile sourceContext base :=
  match derivation with
  | .ofFormation formationTyped =>
      formationClassifierPinned formationTyped rho sourceContext
        coherent.toContextReflectsRename wellFormed subjectInImage
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      let ⟨base, pinConv, baseTyped⟩ :=
        normalClassifierPinnedFlagCoherent residualWithinBudget flagUnique typedPremise
          subjectNormal subjectSize targetWellFormed rho sourceContext rhoInjective coherent
          wellFormed subjectInImage
      ⟨base, converts.sym.trans pinConv, baseTyped⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => by
      obtain ⟨sourceDomain, sourceBody, _hSourceSubject, hDomain, hBody⟩ :=
        renameEqLamCellInversion rho subjectInImage.symm
      have domainNormal := lamNormal_domainNormal _ _ subjectNormal
      have bodyNormal := lamNormal_bodyNormal _ _ subjectNormal
      -- (1) DOMAIN source typing: the annotation's universe typing reflects through the guarded
      --     master (pin = the rename-invariant universe code), then re-pins exactly.
      have domainPin :
          Conv (universeCodeCell domainLevel flag)
            (RawTerm.rename rho (universeCodeCell domainLevel flag)) := by
        rw [rename_universeCodeCell]
        exact Conv.refl _
      obtain ⟨reflectedDomainClassifier, reflectedDomainConv, reflectedDomainTyped⟩ :=
        HasTypeDescPi.pinnedReflectionGuarded
          (residualWithinBudget (Nat.le_of_lt
            (Nat.lt_of_lt_of_le (RawTerm.size_lt_lamCell_domain _ _) subjectSize)))
          flagUnique domainTyped (Nat.le_refl _) domainNormal
          targetWellFormed rho sourceContext rhoInjective coherent.toContextReflectsRename
          wellFormed hDomain domainPin
          ⟨domainLevel.lsucc, flag,
            HasTypeDescPi.ofFormation
              (HasTypeDesc.universeFormation sourceContext domainLevel flag)⟩
      have sourceDomainTyped :
          HasTypeDescPi profile sourceContext sourceDomain
            (universeCodeCell domainLevel flag) :=
        HasTypeDescPi.retypeAtUniverse rho rhoInjective reflectedDomainConv reflectedDomainTyped
      -- (2) the flag-coherent Kripke extension under the binder: the new (source, target) pair is
      --     (sourceDomain, domainCode) with a definitional pin and the shared-universe triple.
      have domainPinned : Conv domainCode (RawTerm.rename rho sourceDomain) := by
        rw [hDomain]
        exact Conv.refl _
      have imageDomainTyped :
          HasTypeDescPi profile targetContext (RawTerm.rename rho sourceDomain)
            (universeCodeCell domainLevel flag) := hDomain ▸ domainTyped
      have coherentUnderBinder :=
        ContextReflectsRenameFlagCoherent.consConv profile coherent domainPinned
          ⟨domainLevel, flag, domainTyped, sourceDomainTyped, imageDomainTyped⟩
      have wellFormedUnderBinder : WfContextDescPi (sourceContext.cons sourceDomain) :=
        ⟨wellFormed, domainLevel, flag, sourceDomainTyped⟩
      have targetWellFormedUnderBinder : WfContextDescPi (targetContext.cons domainCode) :=
        ⟨targetWellFormed, domainLevel, flag, domainTyped⟩
      -- (3) CODOMAIN pin: recurse into the body premise (normal + in-image, one binder deeper).
      obtain ⟨bodyBase, codomainPin, bodyBaseIsType⟩ :=
        normalClassifierPinnedFlagCoherent residualWithinBudget flagUnique bodyTyped bodyNormal
          (Nat.le_of_lt (Nat.lt_of_lt_of_le (RawTerm.size_lt_lamCell_body _ _) subjectSize))
          targetWellFormedUnderBinder (RawRenaming.lift rho) (sourceContext.cons sourceDomain)
          (RawRenaming.lift_injective rhoInjective) coherentUnderBinder wellFormedUnderBinder
          hBody
      -- (4) the recursive pin's ∃-flag validity re-types at the caller's exact (level, flag).
      have bodyBaseAtCallerPair :
          HasTypeDescPi profile (sourceContext.cons sourceDomain) bodyBase
            (universeCodeCell codomainLevel flag) :=
        HasTypeDescPi.pinBaseValidAtCallerPair targetWellFormedUnderBinder coherentUnderBinder
          codomainPin codomainTyped bodyBaseIsType
      -- (5) source Π reassembly at the ONE shared flag.
      refine ⟨piTyCodeCell sourceDomain bodyBase, ?_, ?_⟩
      · rw [rename_piTyCodeCell]
        exact Conv.piTyCode_cong domainPinned codomainPin
      · exact ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
          HasTypeDescPi.piFormationViaGenArm sourceContext sourceDomain bodyBase
            domainLevel codomainLevel flag sourceDomainTyped bodyBaseAtCallerPair⟩
  | @HasTypeDescPi.piElim _ _ _ nestedFunction nestedArgument _ _
      nestedFunctionTyped nestedArgumentTyped => by
      have nestedFunctionNormal := appNormal_functionNormal _ _ subjectNormal
      have nestedArgumentNormal := appNormal_argumentNormal _ _ subjectNormal
      obtain ⟨sourceNestedFunction, sourceNestedArgument, _hSourceSubject,
          hNestedFunction, hNestedArgument⟩ :=
        renameEqAppCellInversion rho subjectInImage.symm
      have nestedFunctionSizeBound : _ ≤ budget :=
        Nat.le_of_lt
          (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_function _ _) subjectSize)
      obtain ⟨piBase, piPinned, piBaseTyped⟩ :=
        normalClassifierPinnedFlagCoherent residualWithinBudget flagUnique nestedFunctionTyped
          nestedFunctionNormal nestedFunctionSizeBound targetWellFormed rho
          sourceContext rhoInjective coherent wellFormed hNestedFunction
      obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
        Conv.pinnedPiComponentsWithSourceChain rho piPinned
      obtain ⟨piLevel, piFlag, piBaseAt⟩ := piBaseTyped
      have piReductTyped :=
        HasTypeDescPi.subjectReductionStar wellFormed piBaseAt sourceChain
      obtain ⟨domainLevel, codomainLevel, componentFlag, domainTyped, codomainTyped,
          _convToOutput⟩ := HasTypeDescPi.invertPiTyCode piReductTyped
      have nestedArgumentSizeBound : _ ≤ budget :=
        Nat.le_of_lt
          (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_argument _ _) subjectSize)
      obtain ⟨argumentReflectedClassifier, argumentClassConv, sourceArgumentTyped⟩ :=
        HasTypeDescPi.pinnedReflectionGuarded (residualWithinBudget nestedArgumentSizeBound)
          flagUnique nestedArgumentTyped (Nat.le_refl _) nestedArgumentNormal
          targetWellFormed rho sourceContext rhoInjective coherent.toContextReflectsRename
          wellFormed hNestedArgument domainConv ⟨domainLevel, componentFlag, domainTyped⟩
      have sourceArgumentAtDomain :
          HasTypeDescPi profile sourceContext sourceNestedArgument domainBase :=
        HasTypeDescPi.conv domainLevel componentFlag sourceArgumentTyped
          (Conv.reflectRenameOfFinInjective rho rhoInjective
            (argumentClassConv.sym.trans domainConv)) domainTyped
      refine ⟨RawTerm.subst0 codomainBase sourceNestedArgument, ?_, ?_⟩
      · rw [RawTerm.rename_subst0_commute, ← hNestedArgument]
        exact Conv.subst _ codomainConv
      · refine ⟨codomainLevel, componentFlag, ?_⟩
        exact HasTypeDescPi.substituteUnderBinding sourceNestedArgument
          codomainTyped sourceArgumentAtDomain
  | .genFormationPi _targetContext generator payload children levels flag rule
      isFormation _premises => by
      -- ROW-SHAPE-AGNOSTIC: the output is SOME universe code (`output_isUniverseCode`); the abstract
      -- `outputLevel`/`outputFlag` replace the pinned `lmaxAll levels`/`flag` (the flag merely rides
      -- into the universe code, not flag-coherence reasoning), so the nullary-row flip absorbs here.
      obtain ⟨outputLevel, outputFlag, hOutput⟩ :=
        typingRuleDescOf_output_isUniverseCode isFormation _ levels flag
      rw [hOutput]
      refine ⟨universeCodeCell outputLevel outputFlag, ?_, ?_⟩
      · rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact ⟨outputLevel.lsucc, outputFlag,
          .ofFormation (.universeFormation sourceContext outputLevel outputFlag)⟩

/-- **The pinned-function piElim core over the flag-coherent motive** — the shipped
`pinnedReflectionPiElimCore` with the premise IHs receiving the coherent condition. -/
theorem pinnedReflectionPiElimCoreFlagCoherent (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)}
    (functionIH : PinnedReflectionConclusionFlagCoherent profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode))
    (argumentIH : PinnedReflectionConclusionFlagCoherent profile targetContext argument
      domainCode)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetWellFormed : WfContextDescPi targetContext)
    (rhoInjective : Function.Injective rho)
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (wellFormed : WfContextDescPi sourceContext)
    {sourceFunction sourceArgument piBase : RawTerm sourceScope}
    (functionInImage : functionTerm = RawTerm.rename rho sourceFunction)
    (argumentInImage : argument = RawTerm.rename rho sourceArgument)
    (piPinned :
      Conv (piTyCodeCell domainCode codomainCode) (RawTerm.rename rho piBase))
    (piBaseTyped : IsTypeDescPi profile sourceContext piBase) :
    ∃ reflectedClassifier : RawTerm sourceScope,
      Conv (RawTerm.subst0 codomainCode argument)
        (RawTerm.rename rho reflectedClassifier) ∧
      HasTypeDescPi profile sourceContext (appCell sourceFunction sourceArgument)
        reflectedClassifier := by
  obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain rho piPinned
  obtain ⟨piLevel, piFlag, piBaseTypedAt⟩ := piBaseTyped
  have piTyped : HasTypeDescPi profile sourceContext
      (piTyCodeCell domainBase codomainBase) (universeCodeCell piLevel piFlag) :=
    HasTypeDescPi.subjectReductionStar wellFormed piBaseTypedAt sourceChain
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, _convToOutput⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  obtain ⟨reflectedFunctionClassifier, functionClassifierConv, functionReflected⟩ :=
    functionIH targetWellFormed rho sourceContext rhoInjective coherent wellFormed
      functionInImage piPinned ⟨piLevel, piFlag, piBaseTypedAt⟩
  have piImagesConv :
      Conv (RawTerm.rename rho reflectedFunctionClassifier)
        (RawTerm.rename rho piBase) :=
    functionClassifierConv.sym.trans piPinned
  have reflectedToPiBase : Conv reflectedFunctionClassifier piBase :=
    Conv.reflectRenameOfFinInjective rho rhoInjective piImagesConv
  have piBaseToPiTyCode : Conv piBase (piTyCodeCell domainBase codomainBase) :=
    ⟨piTyCodeCell domainBase codomainBase, sourceChain, StepStar.refl _⟩
  have functionAtSourcePi :
      HasTypeDescPi profile sourceContext sourceFunction
        (piTyCodeCell domainBase codomainBase) :=
    HasTypeDescPi.conv piLevel piFlag functionReflected
      (reflectedToPiBase.trans piBaseToPiTyCode) piTyped
  obtain ⟨reflectedArgumentClassifier, argumentClassifierConv, argumentReflected⟩ :=
    argumentIH targetWellFormed rho sourceContext rhoInjective coherent wellFormed
      argumentInImage domainConv ⟨domainLevel, flag, domainTyped⟩
  have domainImagesConv :
      Conv (RawTerm.rename rho reflectedArgumentClassifier)
        (RawTerm.rename rho domainBase) :=
    argumentClassifierConv.sym.trans domainConv
  have argumentAtDomainBase :
      HasTypeDescPi profile sourceContext sourceArgument domainBase :=
    HasTypeDescPi.conv domainLevel flag argumentReflected
      (Conv.reflectRenameOfFinInjective rho rhoInjective domainImagesConv) domainTyped
  refine ⟨RawTerm.subst0 codomainBase sourceArgument, ?_, ?_⟩
  · rw [RawTerm.rename_subst0_commute, ← argumentInImage]
    exact Conv.subst _ codomainConv
  · exact HasTypeDescPi.piElim functionAtSourcePi argumentAtDomainBase

/-- ★ **THE FLAG-COHERENT piELIM RESIDUAL HOLDS** — the strengthening campaign's open core,
discharged.  With the λ-INCLUSIVE pin extraction NO head split is needed: grown-wf open SN
normalizes the function, subject reduction keeps the Π classifier on the normal reduct, the
reduct is in-image (`StepStar.reflectRename`), its classifier pins WHATEVER its head
(λ heads via T2 + E3, neutral heads via the spine walk), and the coherent core finishes with
the premise reflections. -/
theorem pinnedReflectionPiElimResidualFlagCoherentHolds (profile : PolyProfile)
    (flagUnique : SourceUniverseFlagUnique profile) :
    PinnedReflectionPiElimResidualFlagCoherent profile := by
  intro targetScope targetContext functionTerm argument domainCode codomainCode
    functionTyped argumentTyped functionIH argumentIH
  intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  have functionStronglyNormalizing : StepStar.IsStronglyNormalizing functionTerm :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDescPi targetWellFormed functionTyped
  obtain ⟨reduct, functionReduces, reductNormal⟩ :
      ∃ reduct : RawTerm targetScope,
        StepStar functionTerm reduct ∧ RawTerm.isStepNormalForm reduct :=
    ⟨RawTerm.normalize functionTerm functionStronglyNormalizing,
      RawTerm.normalize_reducesTo functionTerm functionStronglyNormalizing,
      RawTerm.normalize_isStepNormalForm functionTerm functionStronglyNormalizing⟩
  have reductTyped : HasTypeDescPi profile targetContext reduct
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.subjectReductionStar targetWellFormed functionTyped functionReduces
  rw [hFunction] at functionReduces
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho functionReduces
  obtain ⟨reflectedPiBase, piPinned, piBaseTyped⟩ :=
    normalClassifierPinnedFlagCoherent (budget := reduct.size)
      (fun {smallBound} _withinBudget =>
        piElimResidualGuardedAtEveryBound profile flagUnique smallBound)
      flagUnique reductTyped reductNormal (Nat.le_refl _) targetWellFormed rho sourceContext
      rhoInjective coherent wellFormed imageEq.symm
  exact pinnedReflectionPiElimCoreFlagCoherent profile functionIH argumentIH rho sourceContext
    targetWellFormed rhoInjective coherent wellFormed hFunction hArgument piPinned piBaseTyped

/-- **The named λ-reduct target holds** — `PinnedReflectionPiElimLamReductResidualFlagCoherent`
as a corollary of the head-split-free umbrella discharge (its extra whnf premises are unused). -/
theorem pinnedReflectionPiElimLamReductResidualFlagCoherentHolds (profile : PolyProfile)
    (flagUnique : SourceUniverseFlagUnique profile) :
    PinnedReflectionPiElimLamReductResidualFlagCoherent profile := by
  intro targetScope targetContext functionTerm argument domainCode lamDomain codomainCode lamBody
    functionTyped argumentTyped _functionReduces _reductNormal functionIH argumentIH
  exact pinnedReflectionPiElimResidualFlagCoherentHolds profile flagUnique
    functionTyped argumentTyped functionIH argumentIH

end FX1Poly.Typed
