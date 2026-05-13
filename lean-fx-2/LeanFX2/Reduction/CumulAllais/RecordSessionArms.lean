import LeanFX2.Reduction.CumulAllais.PathArms

/-! # LeanFX2.Reduction.CumulAllais.RecordSessionArms

Allais arms for the record / refine / codata / session / effect
Term constructors:

* Single-field records: `recordIntro`, `recordProj`.
* Refinement types: `refineIntro`, `refineElim`.
* Codata: `codataUnfold`, `codataDest`.
* Session types: `sessionSend`, `sessionRecv`.
* Effects: `effectPerform`.

Each arm recurses on its substituent ConvCumul subterms via the
structural `compat` IHs, then reassembles via the matching
ctor-level cong rule on `ConvCumul`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-- Allais arm for single-field `recordIntro`: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_recordIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {singleFieldType : Ty sourceLevel sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (fieldCompat :
      ConvCumul (firstField.substHet termSubstA)
                (firstField.substHet termSubstB)) :
    ConvCumul ((Term.recordIntro firstField).substHet termSubstA)
              ((Term.recordIntro firstField).substHet termSubstB) :=
  ConvCumul.recordIntroCong fieldCompat

/-- Allais arm for single-field `recordProj`: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_recordProj_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {singleFieldType : Ty sourceLevel sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (recordCompat :
      ConvCumul (recordValue.substHet termSubstA)
                (recordValue.substHet termSubstB)) :
    ConvCumul ((Term.recordProj recordValue).substHet termSubstA)
              ((Term.recordProj recordValue).substHet termSubstB) :=
  ConvCumul.recordProjCong recordCompat

/-- Allais arm for `refineIntro`: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_refineIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {baseType : Ty sourceLevel sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (valueCompat :
      ConvCumul (baseValue.substHet termSubstA)
                (baseValue.substHet termSubstB))
    (proofCompat :
      ConvCumul (predicateProof.substHet termSubstA)
                (predicateProof.substHet termSubstB)) :
    ConvCumul ((Term.refineIntro predicate baseValue predicateProof).substHet termSubstA)
              ((Term.refineIntro predicate baseValue predicateProof).substHet termSubstB) :=
  ConvCumul.refineIntroCong valueCompat proofCompat

/-- Allais arm for `refineElim`: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_refineElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {baseType : Ty sourceLevel sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (refinedValue : Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (refinedCompat :
      ConvCumul (refinedValue.substHet termSubstA)
                (refinedValue.substHet termSubstB)) :
    ConvCumul ((Term.refineElim refinedValue).substHet termSubstA)
              ((Term.refineElim refinedValue).substHet termSubstB) :=
  ConvCumul.refineElimCong refinedCompat

/-- Allais arm for `codataUnfold`: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_codataUnfold_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {stateType outputType : Ty sourceLevel sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (stateCompat :
      ConvCumul (initialState.substHet termSubstA)
                (initialState.substHet termSubstB))
    (transitionCompat :
      ConvCumul (transition.substHet termSubstA)
                (transition.substHet termSubstB)) :
    ConvCumul ((Term.codataUnfold initialState transition).substHet termSubstA)
              ((Term.codataUnfold initialState transition).substHet termSubstB) :=
  ConvCumul.codataUnfoldCong stateCompat transitionCompat

/-- Allais arm for `codataDest`: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_codataDest_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {stateType outputType : Ty sourceLevel sourceScope}
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (codataCompat :
      ConvCumul (codataValue.substHet termSubstA)
                (codataValue.substHet termSubstB)) :
    ConvCumul ((Term.codataDest codataValue).substHet termSubstA)
              ((Term.codataDest codataValue).substHet termSubstB) :=
  ConvCumul.codataDestCong codataCompat

/-- Allais arm for `sessionSend`: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_sessionSend_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty sourceLevel sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (channelCompat :
      ConvCumul (channel.substHet termSubstA)
                (channel.substHet termSubstB))
    (payloadCompat :
      ConvCumul (payload.substHet termSubstA)
                (payload.substHet termSubstB)) :
    ConvCumul ((Term.sessionSend protocolStep channel payload).substHet termSubstA)
              ((Term.sessionSend protocolStep channel payload).substHet termSubstB) :=
  ConvCumul.sessionSendCong channelCompat payloadCompat

/-- Allais arm for `sessionRecv`: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_sessionRecv_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (channelCompat :
      ConvCumul (channel.substHet termSubstA)
                (channel.substHet termSubstB)) :
    ConvCumul ((Term.sessionRecv channel).substHet termSubstA)
              ((Term.sessionRecv channel).substHet termSubstB) :=
  ConvCumul.sessionRecvCong channelCompat

/-- Allais arm for `effectPerform`: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_effectPerform_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (effectTag : RawTerm sourceScope)
    (effectRow : Effects.EffectRow)
    (operationSignature :
      Effects.OperationSignature (Ty sourceLevel sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    (operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (operationCompat :
      ConvCumul (operationTag.substHet termSubstA)
                (operationTag.substHet termSubstB))
    (argumentsCompat :
      ConvCumul (arguments.substHet termSubstA)
                (arguments.substHet termSubstB)) :
    ConvCumul
      ((Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments).substHet termSubstA)
      ((Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments).substHet termSubstB) :=
  ConvCumul.effectPerformCong operationCompat argumentsCompat

end LeanFX2
