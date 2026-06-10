import FX1Poly.Typed.PinnedReflectionFlagCoherentMaster
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Core.StepEtaCriticalPairs

/-! # FX1Poly/Typed/GrownEtaSubjectReduction — η-SR, the λ-arm (STR-10):
     grown typing is preserved by `etaLam` contraction

η-contraction sends `lam domainAnn (app (weaken f) newestVar)` to `f`; re-typing `f` in the
SMALLER scope is exactly strengthening on the function part — the residual that kept this arm
open through the whole strengthening campaign.  With the campaign closed
(`PinnedReflectionFlagCoherentMaster`), the arm is a composition of shipped bricks:

  1. `invertLam` (T2 pin) + `invertApp` expose the body's application typing:
     `weaken f : Π innerDomain innerCodomain` under the binder, `newestVar : innerDomain`,
     and the body classifier `Conv (subst0 innerCodomain newestVar)`.
  2. `invertVar` pins `innerDomain` to the weakened annotation (the cons-lookup at zero IS
     `weaken domainAnn`, definitionally).
  3. The λ-INCLUSIVE pin extraction on the normalized weakened function (open SN + SR-star +
     `StepStar.reflectRename`) pins its Π classifier, and the PREMISE-FREE master reflects the
     typing to the smaller scope: `f : reflectedPi` with
     `Conv (Π innerDomain innerCodomain) (weaken reflectedPi)`.
  4. `pinnedPiComponentsWithSourceChain` exposes `reflectedPi ↝* Π reflectedDomain
     reflectedCodomain` with EXACT-image components; the η-coherence cancellation
     `subst0_lift_weaken_newestVar` collapses the instantiated codomain back to
     `reflectedCodomain`, and `Conv.reflectWeaken` strips the domain weakening — so the
     original λ classifier `Π domainAnn bodyClassifier` is `Conv reflectedPi`, and the grown
     `conv` rule (with classifier validity from the wf context) lands `f` at the ORIGINAL
     classifier.

This is the crux arm of grown βη subject reduction (PAR-2); the structural η arms
(pair/modIntro/glueIntro/pathLam) are the follow-up (STR-11).

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **η-SR, λ-arm (STR-10)**: a grown typing of the function-η source
`lam domainAnn (app (weaken f) newestVar)` in a well-formed context descends to `f` at the SAME
classifier — grown typing is preserved by `Step.eta.etaLam` contraction. -/
theorem HasTypeDescPi.preservedByEtaLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn innerFunction : RawTerm scope} {classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context
      (RawTerm.etaLamSource domainAnn innerFunction) classifier) :
    HasTypeDescPi profile context innerFunction classifier := by
  have lamTyped : HasTypeDescPi profile context
      (lamCell domainAnn
        (appCell (RawTerm.weaken innerFunction) RawTerm.newestVar)) classifier := typed
  obtain ⟨bodyClassifier, domainLevel, codomainLevel, flag, convToPi, domainTyped,
      _bodyClassifierTyped, bodyTyped⟩ := HasTypeDescPi.invertLam lamTyped
  obtain ⟨innerDomain, innerCodomain, weakenedFunctionTyped, argumentTyped,
      bodyClassifierConv⟩ := HasTypeDescPi.invertApp bodyTyped
  have wellFormedUnderBinder : WfContextDescPi (context.cons domainAnn) :=
    ⟨wellFormed, domainLevel, flag, domainTyped⟩
  -- (1) pin the weakened function's Π classifier: normalize, keep the Π by subject reduction,
  --     reflect the chain, extract the pin from the NORMAL reduct (λ-inclusive).
  have functionStronglyNormalizing :
      StepStar.IsStronglyNormalizing (RawTerm.weaken innerFunction) :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDescPi wellFormedUnderBinder
      weakenedFunctionTyped
  obtain ⟨reduct, functionReduces, reductNormal⟩ :
      ∃ reduct : RawTerm (scope + 1),
        StepStar (RawTerm.weaken innerFunction) reduct ∧ RawTerm.isStepNormalForm reduct :=
    ⟨RawTerm.normalize _ functionStronglyNormalizing,
      RawTerm.normalize_reducesTo _ functionStronglyNormalizing,
      RawTerm.normalize_isStepNormalForm _ functionStronglyNormalizing⟩
  have reductTyped : HasTypeDescPi profile (context.cons domainAnn) reduct
      (piTyCodeCell innerDomain innerCodomain) :=
    HasTypeDescPi.subjectReductionStar wellFormedUnderBinder weakenedFunctionTyped
      functionReduces
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename RawRenaming.weaken
      (show StepStar (RawTerm.rename RawRenaming.weaken innerFunction) reduct
        from functionReduces)
  obtain ⟨piBase, piPinned, piBaseTyped⟩ :=
    normalClassifierPinnedFlagCoherent (budget := reduct.size)
      (fun {smallBound} _withinBudget =>
        piElimResidualGuardedAtEveryBound profile (sourceUniverseFlagUniqueHolds profile)
          smallBound)
      (sourceUniverseFlagUniqueHolds profile) reductTyped reductNormal (Nat.le_refl _)
      wellFormedUnderBinder RawRenaming.weaken context RawRenaming.weaken_finInjective
      (ContextReflectsRenameFlagCoherent.ofWeakenCons profile domainAnn wellFormed)
      wellFormed imageEq.symm
  -- (2) reflect the weakened function's typing to the smaller scope (premise-free master).
  obtain ⟨reflectedPi, reflectedPiConv, functionReflected⟩ :=
    HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional weakenedFunctionTyped
      wellFormedUnderBinder RawRenaming.weaken context RawRenaming.weaken_finInjective
      (ContextReflectsRenameFlagCoherent.ofWeakenCons profile domainAnn wellFormed)
      wellFormed
      (show RawTerm.weaken innerFunction
          = RawTerm.rename RawRenaming.weaken innerFunction from rfl)
      piPinned piBaseTyped
  -- (3) the reflected Π's exact-image components.
  obtain ⟨reflectedDomain, reflectedCodomain, reflectedChain, innerDomainConv,
      innerCodomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain RawRenaming.weaken reflectedPiConv
  -- (4) η-coherence, codomain leg: the body classifier collapses to the reflected codomain —
  --     the lifted-weakening substitution at the newest variable is the identity.
  have substConv : Conv (RawTerm.subst0 innerCodomain RawTerm.newestVar)
      (RawTerm.subst0
        (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) reflectedCodomain)
        RawTerm.newestVar) :=
    Conv.subst _ innerCodomainConv
  rw [RawTerm.subst0_lift_weaken_newestVar] at substConv
  have bodyClassifierToReflected : Conv bodyClassifier reflectedCodomain :=
    bodyClassifierConv.trans substConv
  -- (5) η-coherence, domain leg: the inner domain pins to the weakened annotation through the
  --     newest variable's lookup, and `Conv.reflectWeaken` strips the shared weakening.
  have innerDomainToWeakenedAnn :
      Conv innerDomain (RawTerm.rename RawRenaming.weaken domainAnn) :=
    HasTypeDescPi.invertVar argumentTyped
  have annToReflectedDomain : Conv domainAnn reflectedDomain :=
    Conv.reflectWeaken (innerDomainToWeakenedAnn.sym.trans innerDomainConv)
  -- (6) assemble: the original λ classifier is Conv to the reflected classifier.
  have reflectedPiToComponents :
      Conv reflectedPi (piTyCodeCell reflectedDomain reflectedCodomain) :=
    ⟨piTyCodeCell reflectedDomain reflectedCodomain, reflectedChain, StepStar.refl _⟩
  have piComponentsCong :
      Conv (piTyCodeCell domainAnn bodyClassifier)
        (piTyCodeCell reflectedDomain reflectedCodomain) :=
    Conv.piTyCode_cong annToReflectedDomain bodyClassifierToReflected
  have classifierToReflectedPi : Conv classifier reflectedPi :=
    (convToPi.trans piComponentsCong).trans reflectedPiToComponents.sym
  -- (7) land at the ORIGINAL classifier via the grown conv rule (classifier validity from wf).
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
    typed.classifierIsTypeDescPi wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag functionReflected
    classifierToReflectedPi.sym classifierTyped

/-- The arm restated against the `Step.eta` constructor: any `etaLam` contraction instance
preserves grown typing in a well-formed context. -/
theorem HasTypeDescPi.preservedByEtaLamStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn innerFunction : RawTerm scope} {classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context
      (RawTerm.etaLamSource domainAnn innerFunction) classifier)
    (_contracts : Step.eta (RawTerm.etaLamSource domainAnn innerFunction) innerFunction) :
    HasTypeDescPi profile context innerFunction classifier :=
  HasTypeDescPi.preservedByEtaLam wellFormed typed

end FX1Poly.Typed
