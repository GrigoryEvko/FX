import LeanFX2.Term.StrengtheningImage.Core.Base
import LeanFX2.Term.PartialStrengthen.Constructors.ApplicationAndBinders
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Atomic.Cubical

/-! # Term/StrengtheningImage/Binders

Soundness lemmas for lambda and path-lambda strengthening producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for dependent lambda strengthening.

The wrapper takes `body : Term (sourceCtx.cons domainType) codomainType
bodyRaw` and produces `Term.lamPi body`.  The renamedTarget is
`Term.lamPi (Term.rename (strengthening.toTermRenaming.lift _)
targetBodyTerm)` whose body's renaming proof has source context
`sourceCtx.cons (targetDomainType.rename strengthening.forward)`,
whereas `bodySound.termRenames` carries the proof at source context
`sourceCtx.cons domainType`.  These are propositionally equal via
`domainRenames : domainType = targetDomainType.rename strengthening.forward`
but Lean's dependent typing rejects them as different types.  Fix:
`subst domainRenames` early to unify the two contexts, then Lean's
definitional proof irrelevance on `TermRenaming : Prop` discharges the
remaining equality. -/
theorem partialStrengthenTypedLamPi_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift domainType targetDomainType
          domainTypeStrengthens) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedLamPi domainTypeStrengthens bodyResult) := by
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainTypeStrengthens
  subst domainRenames
  cases bodyResult with
  | mk targetCodomainType targetBodyRaw targetBodyTerm
      codomainTypeStrengthens bodyRawStrengthens codomainTypeRenames
      bodyRawRenames =>
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      dsimp [StrengtheningResult.renamedTarget] at bodyHEq
      dsimp [partialStrengthenTypedLamPi, StrengtheningResult.renamedTarget,
        Term.rename]
      exact Term.lamPi_HEq_congr rfl codomainTypeRenames
        bodyRawRenames bodyHEq

/-- Soundness for non-dependent lambda strengthening.

Extends the LamPi `subst-early` recipe with the `.weaken` cast bridge.
Body has type `Term (sourceCtx.cons domainType) codomainType.weaken
bodyRaw`.  `Term.rename` of `Term.lam` (Rename.lean:262-264) introduces
a `Ty.weaken_rename_commute rho codomainType ▸` cast to align the body's
type from `codomainType.weaken.rename rho.lift` to `(codomainType.rename
rho).weaken`.  After `subst domainRenames` + `subst codomainRenames`,
both sides agree on domain and codomain, and the body HEq is bridged
to the casted form via `Term.type_eq_cast_heq`. -/
theorem partialStrengthenTypedLam_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainTypeStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift domainType targetDomainType
          domainTypeStrengthens) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedLam domainTypeStrengthens
        codomainTypeStrengthens bodyResult) := by
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainTypeStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainType codomainTypeStrengthens
  subst domainRenames
  subst codomainRenames
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          Ty.partialStrengthen?
              (Ty.weaken (targetCodomainType.rename strengthening.forward))
              strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have expectedBodyTypeStrengthens :
          Ty.partialStrengthen?
              (Ty.weaken (targetCodomainType.rename strengthening.forward))
              strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift
          (targetCodomainType.rename strengthening.forward)
          strengthening.back, codomainTypeStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      dsimp [StrengtheningResult.renamedTarget] at bodyHEq
      dsimp [partialStrengthenTypedLam, StrengtheningResult.renamedTarget]
      have castedHEq : HEq body
          (Ty.weaken_rename_commute strengthening.forward
              targetCodomainType ▸
            Term.rename
              ((strengthening.lift (targetDomainType.rename
                  strengthening.forward) targetDomainType
                domainTypeStrengthens).toTermRenaming) targetBodyTerm) :=
        HEq.trans bodyHEq
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute strengthening.forward
              targetCodomainType)
            (Term.rename
              ((strengthening.lift (targetDomainType.rename
                  strengthening.forward) targetDomainType
                domainTypeStrengthens).toTermRenaming)
              targetBodyTerm)).symm
      exact Term.lam_HEq_congr rfl rfl bodyRawRenames castedHEq

/-- Soundness for cubical Path-lambda strengthening.

Mirrors `partialStrengthenTypedLam_sound`: pathLam binds `Ty.interval`
(closed, no strengthening dance) and the body's expected type uses
`carrierType.weaken`.  `Term.rename` of `Term.pathLam` introduces the
same `Ty.weaken_rename_commute rho carrierType ▸` cast as Term.lam.

Compared to Lam: only the carrier type is renamed (interval is closed
so no domainRenames step is needed), and three additional explicit
fields — `leftEndpoint`, `rightEndpoint`, the mode-univalent witness —
flow through unchanged because `Ty.path`'s renaming distributes over
them.  `subst carrierRenames` alone replaces `carrierType` with the
renamed target, then the body dance + cast bridge proceeds exactly as
Lam. -/
theorem partialStrengthenTypedPathLam_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftEndpointStrengthens :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightEndpointStrengthens :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift Ty.interval Ty.interval rfl) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedPathLam modeIsUnivalent
        carrierStrengthens leftEndpointStrengthens
        rightEndpointStrengthens bodyResult) := by
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierStrengthens
  have leftEndpointRenames :
      leftEndpoint =
        targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftEndpointStrengthens
  have rightEndpointRenames :
      rightEndpoint =
        targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightEndpointStrengthens
  subst carrierRenames
  subst leftEndpointRenames
  subst rightEndpointRenames
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          Ty.partialStrengthen?
              (Ty.weaken (targetCarrierType.rename strengthening.forward))
              strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have expectedBodyTypeStrengthens :
          Ty.partialStrengthen?
              (Ty.weaken (targetCarrierType.rename strengthening.forward))
              strengthening.back.lift =
            some targetCarrierType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift
          (targetCarrierType.rename strengthening.forward)
          strengthening.back, carrierStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      dsimp [StrengtheningResult.renamedTarget] at bodyHEq
      dsimp [partialStrengthenTypedPathLam,
        StrengtheningResult.renamedTarget]
      have castedHEq : HEq body
          (Ty.weaken_rename_commute strengthening.forward
              targetCarrierType ▸
            Term.rename
              ((strengthening.lift Ty.interval Ty.interval
                rfl).toTermRenaming) targetBodyTerm) :=
        HEq.trans bodyHEq
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute strengthening.forward
              targetCarrierType)
            (Term.rename
              ((strengthening.lift Ty.interval Ty.interval
                rfl).toTermRenaming)
              targetBodyTerm)).symm
      exact Term.pathLam_HEq_congr modeIsUnivalent rfl rfl rfl
        bodyRawRenames castedHEq

end Term

end LeanFX2
