import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! Probe: STR-8 brick 6 — THE MOTIVE + the piIntro arm of the pinned reflection (the historical
wall).  `PinnedReflectionConclusion` is the route-H induction motive (Kripke-quantified over the
renaming/source context, pinned classifier with a source-TYPED pin base, in-image subject).  The
piIntro arm closes end-to-end: λ-head subject inversion → pinning analysis with source chain →
source SR + Π-formation inversion (discharges the source-side universe premises) → Kripke context
extension → body IH at `lift ρ` → re-pin the reflected body classifier via injective Conv
reflection → rebuild `piIntro`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The route-H pinned-reflection motive.**  For a target judgment `Δ ⊢ subject : classifier`:
for every Fin-injective renaming `ρ` and source context `Γ` satisfying the Kripke image condition
(`ContextReflectsRename`, with `Γ` well-formed), if the subject is an EXACT `ρ`-image and the
classifier is `Conv`-PINNED to a `ρ`-image of a source-TYPED base, then the source subject is typed
at a source classifier whose image is `Conv` to the original classifier. -/
def PinnedReflectionConclusion (profile : PolyProfile) {targetScope : Nat}
    (targetContext : TypingContext profile targetScope)
    (subject classifier : RawTerm targetScope) : Prop :=
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

/-- **The piIntro arm of the pinned reflection.**  Consumes the whole brick-1..5 kit. -/
theorem pinnedReflectionPiIntroArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {domainCode : RawTerm targetScope} {codomainCode body : RawTerm (targetScope + 1)}
    (bodyIH :
      PinnedReflectionConclusion profile (targetContext.cons domainCode) body codomainCode) :
    PinnedReflectionConclusion profile targetContext
      (lamCell body) (piTyCodeCell domainCode codomainCode) := by
  intro sourceScope rho sourceContext rhoInjective condition wellFormed
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
  obtain ⟨reflectedCodomain, codomainConvReflected, bodyTyped⟩ :=
    bodyIH (RawRenaming.lift rho) (sourceContext.cons domainBase)
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

#print axioms FX1Poly.Typed.pinnedReflectionPiIntroArm
