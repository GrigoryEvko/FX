import FX1Poly.Typed.GrownPinnedReflection
import FX1Poly.Typed.LamReductResidualDischarge
import FX1Poly.Core.ConvRenameReflection

/-! # FX1Poly/Typed/PinnedReflectionFlagCoherentMaster — ★ THE pinned reflection, fired
     (the conditional master re-threaded over the flag-coherent motive + the discharged residual)

`LamReductResidualDischarge` closed the campaign's open core — the FLAG-COHERENT piElim residual
holds.  This file makes it FIRE: the shipped conditional master (`GrownPinnedReflection`) runs over
the PLAIN motive, whose residual remains open by design (the λ-codomain flag negotiation genuinely
consumes E1's shared-universe triples), so the master's arms are re-threaded over the flag-coherent
motive `PinnedReflectionConclusionFlagCoherent` and the discharged residual plugs in:

  * `pinnedReflectionOfFormationArmFlagCoherent` / `pinnedReflectionConvArmFlagCoherent` — the
    leaf and conversion arms (the formation reflection is pin- and condition-flavor-free; the
    conv arm re-pins through the conversion).
  * `pinnedReflectionPiIntroArmFlagCoherent` — the T2 piIntro arm over the coherent motive.  The
    one genuinely new step vs the shipped plain arm: the Kripke extension under the binder uses
    `ContextReflectsRenameFlagCoherent.consConv` with the DEFINITIONAL-image shared-universe
    triple (T2 pins `domainCode = rename rho sourceDomain`, so all three triple components sit at
    the rule's own `(domainLevel, flag)`).
  * `HasTypeDescPi.pinnedReflectionFlagCoherentConditional` (+ the telescope companion) — the
    coherent conditional master; the telescope heads extend the condition with the same
    definitional-image triples.
  * ★ `HasTypeDescPi.pinnedReflectionFlagCoherent` — THE FIRING: every grown derivation satisfies
    the flag-coherent pinned reflection, threaded on `SourceUniverseFlagUnique`.
  * `sourceUniverseFlagUniqueHolds` — the threaded premise DISCHARGED: this assembly sits above
    the import cycle that forced it (the piIntro arm cannot import
    `convUniverseClassificationUnique`; this file can), so the flag projection closes it.
  * ★★ `HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional` — the premise-free master.
  * ★★★ `HasTypeDescPi.strengthenUnderBinding(Unconditional)` — THE STRENGTHENING CAMPAIGN'S
    ENDPOINT: a grown typing of a weakened subject at a weakened classifier under one extra
    binding reflects to the smaller context AT THE SAME CLASSIFIER.  The master at
    `rho := RawRenaming.weaken` with `ContextReflectsRenameFlagCoherent.ofWeakenCons` (the
    coherent condition from source wf alone), a free `Conv.refl` pin, `Conv.reflectWeaken`, and
    the grown `conv` rule.  Only the natural presuppositions remain: well-formed smaller context,
    the binding and the classifier valid there.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the re-thread adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The `ofFormation` arm over the coherent motive: the formation master reflection is pin-free
and consumes only the projected Conv condition; wrap its output. -/
theorem pinnedReflectionOfFormationArmFlagCoherent (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (formationTyped : HasTypeDesc profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier := by
  intro _targetWellFormed sourceScope rho sourceContext rhoInjective coherent _wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
    HasTypeDesc.pinnedReflection formationTyped rho sourceContext rhoInjective
      coherent.toContextReflectsRename subjectInImage
  exact ⟨reflectedClassifier, classifierConv, HasTypeDescPi.ofFormation reflectedTyped⟩

/-- The grown `conv` arm over the coherent motive: re-pin the premise through the conversion
(same pin base, same base typing) and convert the output back. -/
theorem pinnedReflectionConvArmFlagCoherent (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier reclassifier : RawTerm targetScope}
    (converts : Conv classifier reclassifier)
    (premiseIH :
      PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject reclassifier := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
    premiseIH targetWellFormed rho sourceContext rhoInjective coherent wellFormed
      subjectInImage (converts.trans pinned) pinBaseTyped
  exact ⟨reflectedClassifier, converts.sym.trans classifierConv, reflectedTyped⟩

/-- **The T2 piIntro arm over the flag-coherent motive** — the shipped
`pinnedReflectionPiIntroArm` with the Kripke extension upgraded: the binder pair
`(sourceDomain, domainCode)` enters `ContextReflectsRenameFlagCoherent.consConv` with the
definitional-image shared-universe triple (T2 pins `domainCode = rename rho sourceDomain`, so the
target, source, and image validities all sit at the rule's `(domainLevel, flag)`). -/
theorem pinnedReflectionPiIntroArmFlagCoherent (profile : PolyProfile)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {domainCode : RawTerm targetScope} {codomainCode body : RawTerm (targetScope + 1)}
    {domainLevel : LevelExpr} {flag : UniverseFlag}
    (targetDomainTyped :
      HasTypeDescPi profile targetContext domainCode (universeCodeCell domainLevel flag))
    (domainIH :
      PinnedReflectionConclusionFlagCoherent profile targetContext domainCode
        (universeCodeCell domainLevel flag))
    (bodyIH :
      PinnedReflectionConclusionFlagCoherent profile (targetContext.cons domainCode) body
        codomainCode) :
    PinnedReflectionConclusionFlagCoherent profile targetContext
      (lamCell domainCode body) (piTyCodeCell domainCode codomainCode) := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨sourceDomain, sourceBody, hSubject, hDomain, hBody⟩ :=
    renameEqLamCellInversion rho subjectInImage.symm
  subst hSubject
  obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain rho pinned
  obtain ⟨baseLevel, baseFlag, baseTyped⟩ := pinBaseTyped
  have piTyped : HasTypeDescPi profile sourceContext
      (piTyCodeCell domainBase codomainBase) (universeCodeCell baseLevel baseFlag) :=
    HasTypeDescPi.subjectReductionStar wellFormed baseTyped sourceChain
  obtain ⟨baseDomainLevel, codomainLevel, baseFlag', domainBaseTyped, codomainTyped, _convToOutput⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  -- (1) DOMAIN reflection through its own IH at the rename-invariant universe pin, then the
  --     inlined retype lands `sourceDomain` at the SOURCE-side universe.
  have domainPin :
      Conv (universeCodeCell domainLevel flag)
        (RawTerm.rename rho (universeCodeCell domainLevel flag)) := by
    rw [rename_universeCodeCell]
    exact Conv.refl _
  obtain ⟨reflectedDomainClassifier, reflectedDomainConv, reflectedDomainTyped⟩ :=
    domainIH targetWellFormed rho sourceContext rhoInjective coherent wellFormed
      hDomain domainPin
      ⟨domainLevel.lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation sourceContext domainLevel flag)⟩
  have sourceDomainTyped :
      HasTypeDescPi profile sourceContext sourceDomain (universeCodeCell domainLevel flag) :=
    HasTypeDescPi.retypeAtUniverse rho rhoInjective reflectedDomainConv reflectedDomainTyped
  -- (2) `Conv sourceDomain domainBase`: the inverted domain image fed into the classifier pin,
  --     reflected through `rho`.
  have sourceDomainConvBase : Conv sourceDomain domainBase :=
    Conv.reflectRenameOfFinInjective rho rhoInjective (hDomain ▸ domainConv)
  -- flag coherence: domain (at `flag`) and source-chain codomain (at `baseFlag'`) share a flag.
  have flagsAgree : flag = baseFlag' :=
    flagUnique wellFormed sourceDomainConvBase sourceDomainTyped domainBaseTyped
  subst flagsAgree
  -- (3) push the codomain off the classifier-pinned `domainBase` binder onto `sourceDomain`.
  have restValid : ∀ index : Fin sourceScope,
      IsTypeDescPi profile sourceContext (sourceContext.lookup index) :=
    fun index => WfContextDescPi.lookupIsType sourceContext wellFormed index
  have enriched :
      ConvContextWithOldValid (sourceContext.cons domainBase) (sourceContext.cons sourceDomain) :=
    ConvContextWithOldValid.ofHeadConv ⟨baseDomainLevel, flag, domainBaseTyped⟩ restValid
      sourceDomainConvBase.sym
  have codomainUnderSourceDomain :
      HasTypeDescPi profile (sourceContext.cons sourceDomain) codomainBase
        (universeCodeCell codomainLevel flag) :=
    HasTypeDescPi.contextConversionExact codomainTyped (sourceContext.cons sourceDomain) enriched
  -- (4) body IH at `lift rho` over the `sourceDomain` binder — the COHERENT Kripke extension
  --     fires with the definitional-image triple.
  have domainPinned : Conv domainCode (RawTerm.rename rho sourceDomain) := by
    rw [hDomain]
    exact Conv.refl _
  have imageDomainTyped :
      HasTypeDescPi profile targetContext (RawTerm.rename rho sourceDomain)
        (universeCodeCell domainLevel flag) := hDomain ▸ targetDomainTyped
  have coherentUnderBinder :
      ContextReflectsRenameFlagCoherent profile (RawRenaming.lift rho)
        (sourceContext.cons sourceDomain) (targetContext.cons domainCode) :=
    ContextReflectsRenameFlagCoherent.consConv profile coherent domainPinned
      ⟨domainLevel, flag, targetDomainTyped, sourceDomainTyped, imageDomainTyped⟩
  have wellFormedUnderBinder : WfContextDescPi (sourceContext.cons sourceDomain) :=
    ⟨wellFormed, domainLevel, flag, sourceDomainTyped⟩
  have targetWellFormedUnderBinder : WfContextDescPi (targetContext.cons domainCode) :=
    ⟨targetWellFormed, domainLevel, flag, targetDomainTyped⟩
  obtain ⟨reflectedCodomain, codomainConvReflected, bodyTyped⟩ :=
    bodyIH targetWellFormedUnderBinder (RawRenaming.lift rho) (sourceContext.cons sourceDomain)
      (RawRenaming.lift_injective rhoInjective) coherentUnderBinder wellFormedUnderBinder
      hBody codomainConv ⟨codomainLevel, flag, codomainUnderSourceDomain⟩
  have imagesConv :
      Conv (RawTerm.rename (RawRenaming.lift rho) reflectedCodomain)
        (RawTerm.rename (RawRenaming.lift rho) codomainBase) :=
    codomainConvReflected.sym.trans codomainConv
  have reflectedToBase : Conv reflectedCodomain codomainBase :=
    Conv.reflectLiftRename rho rhoInjective imagesConv
  have bodyAtCodomainBase :
      HasTypeDescPi profile (sourceContext.cons sourceDomain) sourceBody codomainBase :=
    HasTypeDescPi.conv codomainLevel flag bodyTyped reflectedToBase codomainUnderSourceDomain
  refine ⟨piTyCodeCell sourceDomain codomainBase, ?_, ?_⟩
  · rw [rename_piTyCodeCell]
    exact Conv.piTyCode_cong (hDomain ▸ Conv.refl _) codomainConv
  · exact HasTypeDescPi.piIntro domainLevel codomainLevel flag
      sourceDomainTyped codomainUnderSourceDomain bodyAtCodomainBase

mutual

/-- **The coherent conditional master**: every arm discharged over the flag-coherent motive,
piElim consuming the (now-DISCHARGED) coherent residual hypothesis with both premise
reflections. -/
theorem HasTypeDescPi.pinnedReflectionFlagCoherentConditional {profile : PolyProfile}
    (residual : PinnedReflectionPiElimResidualFlagCoherent profile)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier :=
  match derivation with
  | .ofFormation formationTyped =>
      pinnedReflectionOfFormationArmFlagCoherent profile formationTyped
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      pinnedReflectionConvArmFlagCoherent profile converts
        (HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique typedPremise)
  | .piIntro domainLevel _codomainLevel flag domainTyped _codomainTyped bodyTyped =>
      pinnedReflectionPiIntroArmFlagCoherent profile flagUnique domainTyped
        (HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique domainTyped)
        (HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique bodyTyped)
  | .piElim functionTyped argumentTyped =>
      residual functionTyped argumentTyped
        (HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique functionTyped)
        (HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique argumentTyped)
  | .genFormationPi _targetContext generator payload children levels flag rule
      isFormation premises => by
      intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent
        wellFormed sourceSubject pinBase subjectInImage pinned pinBaseTyped
      have hNotVar : generator ≠ Generator.gen_var :=
        formationRuleImpliesNotVariable isFormation
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      obtain ⟨sourcePayload, sourceChildren, hSource, hChildren⟩ :=
        renameEqMkGenInversion rho hNotVar subjectInImage.symm
      subst hSource
      have sourceTelescope :=
        DescTelescopePi.pinnedReflectionTelescopeFlagCoherentConditional residual flagUnique
          premises targetWellFormed rho sourceContext rhoInjective coherent wellFormed
          hChildren
      refine ⟨universeFormerOutput _ levels flag, ?_, ?_⟩
      · show Conv (universeCodeCell (lmaxAll levels) flag)
          (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact HasTypeDescPi.genFormationPi sourceContext generator sourcePayload
          sourceChildren levels flag { outputType := universeFormerOutput }
          isFormation sourceTelescope

/-- The grown telescope reflection leg over the coherent condition — exact-image heads re-pin to
their universe classifiers; binder crossings extend the condition via the COHERENT `consConv`
with the definitional-image shared-universe triple. -/
theorem DescTelescopePi.pinnedReflectionTelescopeFlagCoherentConditional {profile : PolyProfile}
    (residual : PinnedReflectionPiElimResidualFlagCoherent profile)
    (flagUnique : SourceUniverseFlagUnique profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {targetContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile targetContext levels flag children) :
    WfContextDescPi targetContext →
    ∀ {sourceBaseScope : Nat} (rho : RawRenaming sourceBaseScope baseScope)
      (sourceContext : TypingContext profile (sourceBaseScope + currentDepth)),
      Function.Injective rho →
      ContextReflectsRenameFlagCoherent profile (iterateLiftRaw rho currentDepth)
        sourceContext targetContext →
      WfContextDescPi sourceContext →
      ∀ {sourceChildren : RawTermChildren binderShifts sourceBaseScope},
        children = RawTermChildren.rename rho sourceChildren →
        DescTelescopePi profile sourceContext levels flag sourceChildren :=
  match telescope with
  | .nil _targetContext flag => by
      intro _targetWellFormed sourceBaseScope rho sourceContext _rhoInjective
        _coherent _wellFormed sourceChildren hChildren
      cases sourceChildren with
      | childNil => exact DescTelescopePi.nil sourceContext flag
  | .cons _targetContext head headLevel restLevels flag rest headTyped restTyped => by
      intro targetWellFormed sourceBaseScope rho sourceContext rhoInjective coherent
        wellFormed sourceChildren hChildren
      cases sourceChildren with
        | childCons sourceHead sourceRest =>
          have hChildrenReduced :
              RawTermChildren.childCons head rest =
                RawTermChildren.childCons
                  (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead)
                  (RawTermChildren.rename rho sourceRest) := hChildren
          injection hChildrenReduced with hHeadScope hHeadShift hRestShifts hHead hTail
          have headPin :
              Conv (universeCodeCell headLevel flag)
                (RawTerm.rename (iterateLiftRaw rho currentDepth)
                  (universeCodeCell headLevel flag)) := by
            rw [rename_universeCodeCell]
            exact Conv.refl _
          obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
            HasTypeDescPi.pinnedReflectionFlagCoherentConditional residual flagUnique headTyped
              targetWellFormed (iterateLiftRaw rho currentDepth) sourceContext
              (RawRenaming.iterateLiftRaw_injective rhoInjective currentDepth)
              coherent wellFormed hHead headPin
              ⟨headLevel.lsucc, flag,
                HasTypeDescPi.ofFormation
                  (HasTypeDesc.universeFormation sourceContext headLevel flag)⟩
          have sourceHeadTyped :
              HasTypeDescPi profile sourceContext sourceHead
                (universeCodeCell headLevel flag) :=
            HasTypeDescPi.retypeAtUniverse (iterateLiftRaw rho currentDepth)
              (RawRenaming.iterateLiftRaw_injective rhoInjective currentDepth)
              classifierConv reflectedTyped
          have headPinned :
              Conv head
                (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead) :=
            hHead ▸ Conv.refl _
          have imageHeadTyped :
              HasTypeDescPi profile _targetContext
                (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead)
                (universeCodeCell headLevel flag) := hHead ▸ headTyped
          have coherentUnderBinder :
              ContextReflectsRenameFlagCoherent profile
                (iterateLiftRaw rho (currentDepth + 1))
                (sourceContext.cons sourceHead) (_targetContext.cons head) :=
            ContextReflectsRenameFlagCoherent.consConv profile coherent headPinned
              ⟨headLevel, flag, headTyped, sourceHeadTyped, imageHeadTyped⟩
          have wellFormedUnderBinder : WfContextDescPi (sourceContext.cons sourceHead) :=
            ⟨wellFormed, headLevel, flag, sourceHeadTyped⟩
          have targetWellFormedUnderBinder : WfContextDescPi (_targetContext.cons head) :=
            ⟨targetWellFormed, headLevel, flag, headTyped⟩
          exact DescTelescopePi.cons sourceContext sourceHead headLevel restLevels
            flag sourceRest sourceHeadTyped
            (DescTelescopePi.pinnedReflectionTelescopeFlagCoherentConditional residual
              flagUnique restTyped targetWellFormedUnderBinder rho
              (sourceContext.cons sourceHead) rhoInjective
              coherentUnderBinder wellFormedUnderBinder hTail)

end -- mutual

/-- ★ **THE PINNED REFLECTION, FIRED**: every grown derivation satisfies the flag-coherent
pinned reflection — the coherent conditional master at the DISCHARGED residual
(`pinnedReflectionPiElimResidualFlagCoherentHolds`).  The single remaining premise is
`SourceUniverseFlagUnique` (true — `convUniverseClassificationUnique` — but architecturally
downstream of the piIntro arm's import cycle; the consumer discharges it where both are in
scope). -/
theorem HasTypeDescPi.pinnedReflectionFlagCoherent {profile : PolyProfile}
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionFlagCoherentConditional
    (pinnedReflectionPiElimResidualFlagCoherentHolds profile flagUnique)
    flagUnique derivation

/-- **The threaded flag-uniqueness premise HOLDS** — this file sits ABOVE the import cycle that
forced `SourceUniverseFlagUnique` to be a hypothesis (the piIntro arm cannot import
`convUniverseClassificationUnique`; this assembly can), so the premise discharges outright: it
is the flag projection of the Conv-lifted universe-classification uniqueness. -/
theorem sourceUniverseFlagUniqueHolds (profile : PolyProfile) :
    SourceUniverseFlagUnique profile := by
  intro scope context firstSubject secondSubject firstLevel secondLevel firstFlag secondFlag
    wellFormed subjectsConvertible firstClassified secondClassified
  exact (HasTypeDescPi.convUniverseClassificationUnique wellFormed subjectsConvertible
    firstClassified secondClassified).2

/-- ★★ **THE PINNED REFLECTION, PREMISE-FREE**: every grown derivation satisfies the
flag-coherent pinned reflection — the fired master with the flag-uniqueness premise discharged
by `sourceUniverseFlagUniqueHolds`.  No hypotheses beyond the derivation itself. -/
theorem HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionFlagCoherent (sourceUniverseFlagUniqueHolds profile) derivation

/-- The weakening renaming is Fin-injective: `RawRenaming.weaken` is `Fin.succ`, and successor
values are equal only at equal arguments. -/
theorem RawRenaming.weaken_finInjective {scope : Nat} :
    Function.Injective (RawRenaming.weaken : RawRenaming scope (scope + 1)) := by
  intro leftIndex rightIndex imagesEqual
  have valuesEqual : leftIndex.val + 1 = rightIndex.val + 1 := congrArg Fin.val imagesEqual
  exact Fin.ext (Nat.succ.inj valuesEqual)

/-- ★★ **GROWN STRENGTHENING UNDER A BINDING** — the strengthening campaign's endpoint, closed:
a grown typing of a WEAKENED subject at a WEAKENED classifier under one extra binding reflects
to the smaller context AT THE SAME CLASSIFIER.  The fired master at `rho := RawRenaming.weaken`:
`ofWeakenCons` produces the flag-coherent condition from source wf alone (no circularity — its
payload is exactly the strongest one with a non-circular base instance), the pin is free
(`Conv.refl` — the classifier is its own weaken-image), `Conv.reflectWeaken` strips the
weakening off the reflected classifier's Conv, and the grown `conv` rule lands the subject at
the original classifier via its supplied validity. -/
theorem HasTypeDescPi.strengthenUnderBinding {profile : PolyProfile}
    (flagUnique : SourceUniverseFlagUnique profile)
    {scope : Nat} {context : TypingContext profile scope}
    {bindingType subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (bindingIsType : IsTypeDescPi profile context bindingType)
    (classifierIsType : IsTypeDescPi profile context classifier)
    (typed : HasTypeDescPi profile (context.cons bindingType)
      (RawTerm.weaken subject) (RawTerm.weaken classifier)) :
    HasTypeDescPi profile context subject classifier := by
  obtain ⟨bindingLevel, bindingFlag, bindingTyped⟩ := bindingIsType
  have targetWellFormed : WfContextDescPi (context.cons bindingType) :=
    ⟨wellFormed, bindingLevel, bindingFlag, bindingTyped⟩
  have pinned : Conv (RawTerm.weaken classifier)
      (RawTerm.rename RawRenaming.weaken classifier) := Conv.refl _
  obtain ⟨reflectedClassifier, reflectedConv, reflectedTyped⟩ :=
    HasTypeDescPi.pinnedReflectionFlagCoherent flagUnique typed targetWellFormed
      RawRenaming.weaken context RawRenaming.weaken_finInjective
      (ContextReflectsRenameFlagCoherent.ofWeakenCons profile bindingType wellFormed)
      wellFormed
      (show RawTerm.weaken subject = RawTerm.rename RawRenaming.weaken subject from rfl)
      pinned classifierIsType
  have weakenedClassifiersConv : Conv (RawTerm.weaken classifier)
      (RawTerm.weaken reflectedClassifier) := reflectedConv
  have classifiersConv : Conv classifier reflectedClassifier :=
    Conv.reflectWeaken weakenedClassifiersConv
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ := classifierIsType
  exact HasTypeDescPi.conv classifierLevel classifierFlag reflectedTyped
    classifiersConv.sym classifierTyped

/-- ★★★ **GROWN STRENGTHENING, PREMISE-FREE** — the campaign endpoint with the flag-uniqueness
premise discharged: only the natural presuppositions remain (well-formed smaller context, the
binding and the classifier valid there). -/
theorem HasTypeDescPi.strengthenUnderBindingUnconditional {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {bindingType subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (bindingIsType : IsTypeDescPi profile context bindingType)
    (classifierIsType : IsTypeDescPi profile context classifier)
    (typed : HasTypeDescPi profile (context.cons bindingType)
      (RawTerm.weaken subject) (RawTerm.weaken classifier)) :
    HasTypeDescPi profile context subject classifier :=
  HasTypeDescPi.strengthenUnderBinding (sourceUniverseFlagUniqueHolds profile)
    wellFormed bindingIsType classifierIsType typed

end FX1Poly.Typed
