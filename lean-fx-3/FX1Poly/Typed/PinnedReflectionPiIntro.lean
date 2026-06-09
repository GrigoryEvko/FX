import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/PinnedReflectionPiIntro — THE MOTIVE + the piIntro arm of the pinned reflection
     (route-H reflection brick 6 — the historical wall)

The strengthening campaign's binder arm — the freely-chosen-domain wall that produced the STR-1 and
STR-5b refutations — closes under the pinned motive.  This file ships:

  * `PinnedReflectionConclusion` — THE route-H induction motive.  For a target judgment
    `Δ ⊢ subject : classifier`: for every Fin-injective `ρ` and well-formed source context `Γ`
    satisfying the Kripke image condition, if the subject is an EXACT `ρ`-image and the classifier
    is `Conv`-PINNED to a `ρ`-image of a source-TYPED base, then the source subject is typed at a
    source classifier whose image is `Conv` to the original classifier.
  * `pinnedReflectionPiIntroArm` — the piIntro arm, end-to-end.  The proof composes the whole
    brick-1..5 kit:
      1. `renameEqLamCellInversion` destructures the in-image λ subject;
      2. `Conv.pinnedPiComponentsWithSourceChain` converts the pin into EXACT image components plus
         the SOURCE chain `classifierBase ↝* piTyCodeCell domainBase codomainBase`;
      3. source `subjectReductionStar` + `invertPiTyCode` type `domainBase` / `codomainBase` at
         universes on the SOURCE side (discharging the rebuilt rule's side premises — the step the
         pre-pin designs could not perform);
      4. `ContextReflectsRename.consConv` extends the Kripke condition under the binder;
      5. the body IH fires at `lift ρ` with the codomain pin;
      6. `Conv.reflectLiftRename` (term-level rename injectivity) re-pins the reflected body
         classifier to `codomainBase`, and `HasTypeDescPi.conv` + `piIntro` rebuild.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The route-H pinned-reflection motive.**  For a target judgment `Δ ⊢ subject : classifier`
in a WELL-FORMED target context: for every Fin-injective renaming `ρ` and source context `Γ`
satisfying the Kripke image condition (`ContextReflectsRename`, with `Γ` well-formed), if the
subject is an EXACT `ρ`-image and the classifier is `Conv`-PINNED to a `ρ`-image of a source-TYPED
base, then the source subject is typed at a source classifier whose image is `Conv` to the original
classifier.  Target-side well-formedness is the leading premise: the piElim residual's discharge
routes (whnf-to-head-rigid, the Abel-reflection spine) need TARGET-side SN and subject reduction,
both `WfContextDescPi`-conditional; STR-9's strengthening instance has it freely. -/
def PinnedReflectionConclusion (profile : PolyProfile) {targetScope : Nat}
    (targetContext : TypingContext profile targetScope)
    (subject classifier : RawTerm targetScope) : Prop :=
  WfContextDescPi targetContext →
  ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope),
    Function.Injective rho →
    ContextReflectsRename profile rho sourceContext targetContext →
    WfContextDescPi sourceContext →
    ∀ {sourceSubject pinBase : RawTerm sourceScope},
      subject = RawTerm.rename rho sourceSubject →
      Conv classifier (RawTerm.rename rho pinBase) →
      IsTypeDescPi profile sourceContext pinBase →
      ∃ reflectedClassifier : RawTerm sourceScope,
        Conv classifier (RawTerm.rename rho reflectedClassifier) ∧
        HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier

/-- **The piIntro arm of the pinned reflection** — the historical strengthening wall, closed by the
brick-1..5 kit (see the module docstring for the six-step composition).  The domain's target-side
type validity (`targetDomainIsType`, the rule's own domain premise) extends target well-formedness
under the binder for the body IH. -/
theorem pinnedReflectionPiIntroArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {domainCode : RawTerm targetScope} {codomainCode body : RawTerm (targetScope + 1)}
    (targetDomainIsType : IsTypeDescPi profile targetContext domainCode)
    (bodyIH :
      PinnedReflectionConclusion profile (targetContext.cons domainCode) body codomainCode) :
    PinnedReflectionConclusion profile targetContext
      (lamCell body) (piTyCodeCell domainCode codomainCode) := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨sourceBody, hSubject, hBody⟩ := renameEqLamCellInversion rho subjectInImage.symm
  subst hSubject
  obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain rho pinned
  obtain ⟨baseLevel, baseFlag, baseTyped⟩ := pinBaseTyped
  have piTyped : HasTypeDescPi profile sourceContext
      (piTyCodeCell domainBase codomainBase) (universeCodeCell baseLevel baseFlag) :=
    HasTypeDescPi.subjectReductionStar wellFormed baseTyped sourceChain
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, _convToOutput⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  have condition' :
      ContextReflectsRename profile (RawRenaming.lift rho)
        (sourceContext.cons domainBase) (targetContext.cons domainCode) :=
    ContextReflectsRename.consConv profile condition domainConv
  have wellFormed' : WfContextDescPi (sourceContext.cons domainBase) :=
    ⟨wellFormed, domainLevel, flag, domainTyped⟩
  obtain ⟨targetDomainLevel, targetDomainFlag, targetDomainTyped⟩ := targetDomainIsType
  have targetWellFormed' : WfContextDescPi (targetContext.cons domainCode) :=
    ⟨targetWellFormed, targetDomainLevel, targetDomainFlag, targetDomainTyped⟩
  obtain ⟨reflectedCodomain, codomainConvReflected, bodyTyped⟩ :=
    bodyIH targetWellFormed' (RawRenaming.lift rho) (sourceContext.cons domainBase)
      (RawRenaming.lift_injective rhoInjective) condition' wellFormed'
      hBody codomainConv ⟨codomainLevel, flag, codomainTyped⟩
  have imagesConv :
      Conv (RawTerm.rename (RawRenaming.lift rho) reflectedCodomain)
        (RawTerm.rename (RawRenaming.lift rho) codomainBase) :=
    codomainConvReflected.sym.trans codomainConv
  have reflectedToBase : Conv reflectedCodomain codomainBase :=
    Conv.reflectLiftRename rho rhoInjective imagesConv
  have bodyAtCodomainBase :
      HasTypeDescPi profile (sourceContext.cons domainBase) sourceBody codomainBase :=
    HasTypeDescPi.conv codomainLevel flag bodyTyped reflectedToBase codomainTyped
  refine ⟨piTyCodeCell domainBase codomainBase, ?_, ?_⟩
  · rw [rename_piTyCodeCell]
    exact Conv.piTyCode_cong domainConv codomainConv
  · exact HasTypeDescPi.piIntro domainLevel codomainLevel flag
      domainTyped codomainTyped bodyAtCodomainBase

end FX1Poly.Typed
