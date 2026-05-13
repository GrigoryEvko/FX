import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # LeanFX2.Term.Pointwise.CubicalAndStructuralArms

weaken-subst-singleton arms for the cubical fragment (funextRefl,
funextReflAtId, glueIntro, transp, hcomp) and structural data forms
(record intro, refinement intro/elim, codata unfold, session send/recv).

## Root status

Kernel — cubical and structural arms of the Pointwise
weaken-then-singleton cascade. -/

namespace LeanFX2

/-- Canonical funext reflexivity preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_funextRefl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.funextRefl (context := context) domainType codomainType
            applyRaw)))
      (Term.funextRefl (context := context) domainType codomainType
        applyRaw) := by
  simp only [Term.weaken, Term.rename]
  let renamedFunext :=
    Term.funextRefl (context := context.cons newType)
      (domainType.rename RawRenaming.weaken)
      (codomainType.rename RawRenaming.weaken)
      (applyRaw.rename RawRenaming.weaken.lift)
  let renamedTypeEq :=
    funextReflType_rename RawRenaming.weaken domainType codomainType
      applyRaw
  let substitutedFunextWithCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      (renamedTypeEq.symm ▸ renamedFunext)
  let substitutedTypeEq :=
    funextReflType_subst (Subst.singleton newType singletonRaw)
      (domainType.rename RawRenaming.weaken)
      (codomainType.rename RawRenaming.weaken)
      (applyRaw.rename RawRenaming.weaken.lift)
  have innerCastHEq :
      HEq substitutedFunextWithCast
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedFunext) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      renamedTypeEq.symm
      renamedFunext
  have outerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedFunext)
        (Term.funextRefl (context := context)
          ((domainType.rename RawRenaming.weaken).subst
            (Subst.singleton newType singletonRaw))
          ((codomainType.rename RawRenaming.weaken).subst
            (Subst.singleton newType singletonRaw))
          ((applyRaw.rename RawRenaming.weaken.lift).subst
            (Subst.singleton newType singletonRaw).forRaw.lift)) := by
    exact Term.type_eq_cast_heq substitutedTypeEq.symm
      (Term.funextRefl (context := context)
        ((domainType.rename RawRenaming.weaken).subst
          (Subst.singleton newType singletonRaw))
        ((codomainType.rename RawRenaming.weaken).subst
          (Subst.singleton newType singletonRaw))
        ((applyRaw.rename RawRenaming.weaken.lift).subst
          (Subst.singleton newType singletonRaw).forRaw.lift))
  have constructorHEq :
      HEq
        (Term.funextRefl (context := context)
          ((domainType.rename RawRenaming.weaken).subst
            (Subst.singleton newType singletonRaw))
          ((codomainType.rename RawRenaming.weaken).subst
            (Subst.singleton newType singletonRaw))
          ((applyRaw.rename RawRenaming.weaken.lift).subst
            (Subst.singleton newType singletonRaw).forRaw.lift))
        (Term.funextRefl (context := context) domainType codomainType
          applyRaw) := by
    exact Term.funextRefl_HEq_congr
      (Ty.weaken_subst_singleton domainType newType singletonRaw)
      (Ty.weaken_subst_singleton codomainType newType singletonRaw)
      (RawTerm.weaken_lift_subst_singleton_lift applyRaw singletonRaw)
  exact HEq.trans innerCastHEq (HEq.trans outerCastHEq constructorHEq)

/-- Id-typed funext reflexivity witnesses preserve weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_funextReflAtId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.funextReflAtId (context := context) domainType codomainType
            applyRaw)))
      (Term.funextReflAtId (context := context) domainType codomainType
        applyRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.funextReflAtId_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyRaw singletonRaw)

/-- Glue introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_glueIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness baseRaw partialRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseValue))
        baseValue)
    (partialHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType partialValue))
        partialValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue)))
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.glueIntro_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_subst_singleton boundaryWitness singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton partialRaw singletonRaw)
    baseHEq partialHEq

/-- Cubical transport preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_transp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (pathHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType typePath))
        typePath)
    (sourceHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType sourceValue))
        sourceValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.transp modeIsUnivalent universeLevel universeLevelLt
            sourceType targetType sourceTypeRaw targetTypeRaw typePath
            sourceValue)))
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
    (Ty.weaken_subst_singleton sourceType newType singletonRaw)
    (Ty.weaken_subst_singleton targetType newType singletonRaw)
    (RawTerm.weaken_subst_singleton sourceTypeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton targetTypeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton pathRaw singletonRaw)
    (RawTerm.weaken_subst_singleton sourceRaw singletonRaw)
    pathHEq sourceHEq

/-- Homogeneous composition preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_hcomp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType sidesValue))
        sidesValue)
    (capHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType capValue))
        capValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.hcomp modeIsUnivalent sidesValue capValue)))
      (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.hcomp_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton carrierType newType singletonRaw)
    (RawTerm.weaken_subst_singleton sidesRaw singletonRaw)
    (RawTerm.weaken_subst_singleton capRaw singletonRaw)
    sidesHEq capHEq

/-- Record introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_recordIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (firstField : Term context singleFieldType firstRaw)
    (firstHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType firstField))
        firstField) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.recordIntro firstField)))
      (Term.recordIntro firstField) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.recordIntro_HEq_congr
    (Ty.weaken_subst_singleton singleFieldType newType singletonRaw)
    (RawTerm.weaken_subst_singleton firstRaw singletonRaw)
    firstHEq

/-- Refinement introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refineIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (baseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseValue))
        baseValue)
    (proofHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType predicateProof))
        predicateProof) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.refineIntro predicate baseValue predicateProof)))
      (Term.refineIntro predicate baseValue predicateProof) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.refineIntro_HEq_congr
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift predicate singletonRaw)
    (RawTerm.weaken_subst_singleton valueRaw singletonRaw)
    (RawTerm.weaken_subst_singleton proofRaw singletonRaw)
    baseHEq proofHEq

/-- Refinement elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refineElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType refinedValue))
        refinedValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.refineElim refinedValue)))
      (Term.refineElim refinedValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.refineElim_HEq_congr
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift predicate singletonRaw)
    (RawTerm.weaken_subst_singleton refinedRaw singletonRaw)
    refinedHEq

/-- Codata unfold preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_codataUnfold_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType initialState))
        initialState)
    (transitionHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType transition))
        transition) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.codataUnfold initialState transition)))
      (Term.codataUnfold initialState transition) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.codataUnfold_HEq_congr
    (Ty.weaken_subst_singleton stateType newType singletonRaw)
    (Ty.weaken_subst_singleton outputType newType singletonRaw)
    (RawTerm.weaken_subst_singleton stateRaw singletonRaw)
    (RawTerm.weaken_subst_singleton transitionRaw singletonRaw)
    stateHEq transitionHEq

/-- Session send preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sessionSend_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType channel))
        channel)
    (payloadHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType payload))
        payload) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sessionSend protocolStep channel payload)))
      (Term.sessionSend protocolStep channel payload) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sessionSend_HEq_congr
    (RawTerm.weaken_subst_singleton protocolStep singletonRaw)
    (Ty.weaken_subst_singleton payloadType newType singletonRaw)
    (RawTerm.weaken_subst_singleton channelRaw singletonRaw)
    (RawTerm.weaken_subst_singleton payloadRaw singletonRaw)
    channelHEq payloadHEq

/-- Session receive preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sessionRecv_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep channelRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType channel))
        channel) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.sessionRecv channel)))
      (Term.sessionRecv channel) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sessionRecv_HEq_congr
    (RawTerm.weaken_subst_singleton protocolStep singletonRaw)
    (RawTerm.weaken_subst_singleton channelRaw singletonRaw)
    channelHEq

end LeanFX2
