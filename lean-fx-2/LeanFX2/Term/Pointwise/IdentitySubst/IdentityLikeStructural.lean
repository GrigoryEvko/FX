import LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeEliminators

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeStructural

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

theorem Term.subst_identityLike_pathApp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathHEq :
      HEq (Term.subst termSubst pathTerm) pathTerm)
    (intervalHEq :
      HEq (Term.subst termSubst intervalTerm) intervalTerm) :
    HEq
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.pathApp_HEq_congr
    modeIsUnivalent
    (substitutionIsIdentityLike.tySubst_eq carrierType)
    (substitutionIsIdentityLike.rawSubst_eq leftEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq rightEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq pathRaw)
    (substitutionIsIdentityLike.rawSubst_eq intervalRaw)
    pathHEq intervalHEq

/-- Glue introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_glueIntro_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseHEq :
      HEq (Term.subst termSubst baseValue) baseValue)
    (partialHEq :
      HEq (Term.subst termSubst partialValue) partialValue) :
    HEq
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue))
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.glueIntro_HEq_congr
    modeIsUnivalent
    (substitutionIsIdentityLike.tySubst_eq baseType)
    (substitutionIsIdentityLike.rawSubst_eq boundaryWitness)
    (substitutionIsIdentityLike.rawSubst_eq baseRaw)
    (substitutionIsIdentityLike.rawSubst_eq partialRaw)
    baseHEq partialHEq

/-- Glue elimination case for an identity-like substitution. -/
theorem Term.subst_identityLike_glueElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness)
      gluedRaw)
    (gluedHEq :
      HEq (Term.subst termSubst gluedValue) gluedValue) :
    HEq
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedValue))
      (Term.glueElim modeIsUnivalent gluedValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.glueElim_HEq_congr
    modeIsUnivalent
    (substitutionIsIdentityLike.tySubst_eq baseType)
    (substitutionIsIdentityLike.rawSubst_eq boundaryWitness)
    (substitutionIsIdentityLike.rawSubst_eq gluedRaw)
    gluedHEq

/-- Homogeneous composition case for an identity-like substitution. -/
theorem Term.subst_identityLike_hcomp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesHEq :
      HEq (Term.subst termSubst sidesValue) sidesValue)
    (capHEq :
      HEq (Term.subst termSubst capValue) capValue) :
    HEq
      (Term.subst termSubst
        (Term.hcomp modeIsUnivalent sidesValue capValue))
      (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.hcomp_HEq_congr
    modeIsUnivalent
    (substitutionIsIdentityLike.tySubst_eq carrierType)
    (substitutionIsIdentityLike.rawSubst_eq sidesRaw)
    (substitutionIsIdentityLike.rawSubst_eq capRaw)
    sidesHEq capHEq

/-- Record introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_recordIntro_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (firstFieldHEq :
      HEq (Term.subst termSubst firstField) firstField) :
    HEq
      (Term.subst termSubst (Term.recordIntro firstField))
      (Term.recordIntro firstField) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.recordIntro_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq singleFieldType)
    (substitutionIsIdentityLike.rawSubst_eq firstRaw)
    firstFieldHEq

/-- Record projection case for an identity-like substitution. -/
theorem Term.subst_identityLike_recordProj_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordHEq :
      HEq (Term.subst termSubst recordValue) recordValue) :
    HEq
      (Term.subst termSubst (Term.recordProj recordValue))
      (Term.recordProj recordValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.recordProj_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq singleFieldType)
    (substitutionIsIdentityLike.rawSubst_eq recordRaw)
    recordHEq

/-- Refinement elimination case for an identity-like substitution. -/
theorem Term.subst_identityLike_refineElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (refinedHEq :
      HEq (Term.subst termSubst refinedValue) refinedValue) :
    HEq
      (Term.subst termSubst (Term.refineElim refinedValue))
      (Term.refineElim refinedValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.refineElim_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq baseType)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq predicate)
    (substitutionIsIdentityLike.rawSubst_eq refinedRaw)
    refinedHEq

/-- Codata unfold case for an identity-like substitution. -/
theorem Term.subst_identityLike_codataUnfold_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType)
      transitionRaw)
    (initialStateHEq :
      HEq (Term.subst termSubst initialState) initialState)
    (transitionHEq :
      HEq (Term.subst termSubst transition) transition) :
    HEq
      (Term.subst termSubst
        (Term.codataUnfold initialState transition))
      (Term.codataUnfold initialState transition) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.codataUnfold_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq stateType)
    (substitutionIsIdentityLike.tySubst_eq outputType)
    (substitutionIsIdentityLike.rawSubst_eq stateRaw)
    (substitutionIsIdentityLike.rawSubst_eq transitionRaw)
    initialStateHEq transitionHEq

/-- Codata destructor case for an identity-like substitution. -/
theorem Term.subst_identityLike_codataDest_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType)
      codataRaw)
    (codataHEq :
      HEq (Term.subst termSubst codataValue) codataValue) :
    HEq
      (Term.subst termSubst (Term.codataDest codataValue))
      (Term.codataDest codataValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.codataDest_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq stateType)
    (substitutionIsIdentityLike.tySubst_eq outputType)
    (substitutionIsIdentityLike.rawSubst_eq codataRaw)
    codataHEq

/-- Session send case for an identity-like substitution. -/
theorem Term.subst_identityLike_sessionSend_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (channelHEq :
      HEq (Term.subst termSubst channel) channel)
    (payloadHEq :
      HEq (Term.subst termSubst payload) payload) :
    HEq
      (Term.subst termSubst
        (Term.sessionSend protocolStep channel payload))
      (Term.sessionSend protocolStep channel payload) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.sessionSend_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq protocolStep)
    (substitutionIsIdentityLike.tySubst_eq payloadType)
    (substitutionIsIdentityLike.rawSubst_eq channelRaw)
    (substitutionIsIdentityLike.rawSubst_eq payloadRaw)
    channelHEq payloadHEq

/-- Session receive case for an identity-like substitution. -/
theorem Term.subst_identityLike_sessionRecv_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelHEq :
      HEq (Term.subst termSubst channel) channel) :
    HEq
      (Term.subst termSubst (Term.sessionRecv channel))
      (Term.sessionRecv channel) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.sessionRecv_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq protocolStep)
    (substitutionIsIdentityLike.rawSubst_eq channelRaw)
    channelHEq

/-- Universe cumulativity marker case for an identity-like substitution. -/
theorem Term.subst_identityLike_cumulUp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeHEq :
      HEq (Term.subst termSubst typeCode) typeCode) :
    HEq
      (Term.subst termSubst
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh typeCode))
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.cumulUp_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq codeRaw)
    typeCodeHEq

/-- Equivalence application case for an identity-like substitution. -/
theorem Term.subst_identityLike_equivApp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst termSubst equivTerm) equivTerm)
    (argumentHEq :
      HEq (Term.subst termSubst argumentTerm) argumentTerm) :
    HEq
      (Term.subst termSubst (Term.equivApp equivTerm argumentTerm))
      (Term.equivApp equivTerm argumentTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.equivApp_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrierA)
    (substitutionIsIdentityLike.tySubst_eq carrierB)
    (substitutionIsIdentityLike.rawSubst_eq equivRaw)
    (substitutionIsIdentityLike.rawSubst_eq argumentRaw)
    equivHEq argumentHEq

/-- Univalence beta application case for an identity-like substitution. -/
theorem Term.subst_identityLike_equivApply_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst termSubst equivTerm) equivTerm)
    (argumentHEq :
      HEq (Term.subst termSubst argumentTerm) argumentTerm) :
    HEq
      (Term.subst termSubst (Term.equivApply equivTerm argumentTerm))
      (Term.equivApply equivTerm argumentTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.equivApply_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrierA)
    (substitutionIsIdentityLike.tySubst_eq carrierB)
    (substitutionIsIdentityLike.rawSubst_eq equivRaw)
    (substitutionIsIdentityLike.rawSubst_eq argumentRaw)
    equivHEq argumentHEq

end LeanFX2
