import LeanFX2.Reducibility.TypedCR2Wrapup.LeafFundamentals

/-! # LeanFX2.Reducibility.TypedCR2Wrapup.IntervalSessionEffect

Fundamental + `_stable` cases for the cubical interval ops
(`intervalOpp`/`intervalMeet`/`intervalJoin`) plus the session
(`sessionRecv`/`sessionSend`) and effect (`effectPerform`)
constructors.

## Root status

Layer 3 metatheory leaf.  Second slice of the K12.20.U wrap-up. -/

namespace LeanFX2


/-- **K12.20.AO.1 intervalOpp fundamental case** — cubical interval
negation.  Unary intro to the closed-leaf `Ty.interval`; identical
single-line pattern as `fundamental_natSucc`. -/
theorem Reducible.fundamental_intervalOpp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.intervalOpp innerValue)) :=
  RawTerm.intervalOpp_isStronglyNormalizing innerIH

/-- Interval negation preserves fundamental stability. -/
theorem Reducible.fundamental_intervalOpp_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.intervalOpp innerValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalOpp_isStronglyNormalizing
    (innerIsStable rhoIsInjective termRenaming)

/-- **K12.20.AO.2 intervalMeet fundamental case** — cubical interval
meet (∧).  Binary intro to `Ty.interval`; both subterms substitute
componentwise and the binary SN helper closes both arguments. -/
theorem Reducible.fundamental_intervalMeet
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalMeet leftValue rightValue)) :=
  RawTerm.intervalMeet_isStronglyNormalizing leftIH rightIH

/-- Interval meet preserves fundamental stability. -/
theorem Reducible.fundamental_intervalMeet_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst leftValue))
    (rightIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst rightValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.intervalMeet leftValue rightValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalMeet_isStronglyNormalizing
    (leftIsStable rhoIsInjective termRenaming)
    (rightIsStable rhoIsInjective termRenaming)

/-- **K12.20.AO.3 intervalJoin fundamental case** — cubical interval
join (∨).  Sister to intervalMeet; same binary shape. -/
theorem Reducible.fundamental_intervalJoin
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalJoin leftValue rightValue)) :=
  RawTerm.intervalJoin_isStronglyNormalizing leftIH rightIH

/-- Interval join preserves fundamental stability. -/
theorem Reducible.fundamental_intervalJoin_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst leftValue))
    (rightIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst rightValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.intervalJoin leftValue rightValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalJoin_isStronglyNormalizing
    (leftIsStable rhoIsInjective termRenaming)
    (rightIsStable rhoIsInjective termRenaming)

/-- **K12.20.AP.1 sessionRecv fundamental case** — session-type
receive operation.  Result type `Ty.session protocolStep` is
SN-direct (`Reducibility.lean:667`); `Term.subst` distributes
componentwise over `sessionRecv`
(`LeanFX2/Term/Subst.lean:363-364`); the unary K12.20.AL.1 SN
helper closes the proof in one line. -/
theorem Reducible.fundamental_sessionRecv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.sessionRecv channel)) :=
  RawTerm.sessionRecv_isStronglyNormalizing channelIH

/-- Session receive preserves fundamental stability. -/
theorem Reducible.fundamental_sessionRecv_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst channel)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst (Term.sessionRecv channel)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.sessionRecv_isStronglyNormalizing
    (channelIsStable rhoIsInjective termRenaming)

/-- **K12.20.AP.2 sessionSend fundamental case** — session-type
send operation bundles a channel with an arbitrary-typed payload.
Channel lives at `Ty.session protocolStep` (SN-direct) so `channelIH`
IS SN; payload lives at arbitrary `payloadType`, so its SN witness
is extracted via the K12.18 closure-elimination lemma
`Reducible.isStronglyNormalizing` (lines 639-669) before feeding
the K12.20.AL.2 binary helper. -/
theorem Reducible.fundamental_sessionSend
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel))
    (payloadIH : Reducible (payloadType.subst sigma)
                           (Term.subst termSubst payload)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst
                (Term.sessionSend protocolStep channel payload)) :=
  RawTerm.sessionSend_isStronglyNormalizing channelIH
    (Reducible.isStronglyNormalizing payloadIH)

/-- Session send preserves fundamental stability. -/
theorem Reducible.fundamental_sessionSend_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst channel))
    (payloadIsStable :
      IsRenamingStableReducible (payloadType.subst sigma)
        (Term.subst termSubst payload)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst
        (Term.sessionSend protocolStep channel payload)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.sessionSend_isStronglyNormalizing
    (channelIsStable rhoIsInjective termRenaming)
    (Reducible.isStronglyNormalizing
      (payloadIsStable rhoIsInjective termRenaming))

/-- **K12.20.AQ effectPerform fundamental case** — algebraic effect
operation invocation bundles an operation tag with arguments.
Both subterms have arbitrary-Ty payloads — operationTag at
`Ty.effect operationSignature.argumentCarrier effectTag` (SN-direct
per Reducibility.lean:668 so operationIH IS SN); arguments at
the arbitrary `operationSignature.argumentCarrier` (needs SN
extraction via `Reducible.isStronglyNormalizing` per K12.20.AP.2).
Result type `Ty.effect resultCarrier effectTag` after subst is
also SN-direct.  The K12.20.AL.3 binary SN helper closes the
proof in one line. -/
theorem Reducible.fundamental_effectPerform
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIH :
      Reducible
        ((Ty.effect operationSignature.argumentCarrier effectTag).subst sigma)
        (Term.subst termSubst operationTag))
    (argumentsIH :
      Reducible (operationSignature.argumentCarrier.subst sigma)
                (Term.subst termSubst arguments)) :
    Reducible
      ((Ty.effect operationSignature.resultCarrier effectTag).subst sigma)
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)) :=
  RawTerm.effectPerform_isStronglyNormalizing operationIH
    (Reducible.isStronglyNormalizing argumentsIH)

/-- Effect performance preserves fundamental stability. -/
theorem Reducible.fundamental_effectPerform_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIsStable :
      IsRenamingStableReducible
        ((Ty.effect operationSignature.argumentCarrier effectTag).subst sigma)
        (Term.subst termSubst operationTag))
    (argumentsAreStable :
      IsRenamingStableReducible
        (operationSignature.argumentCarrier.subst sigma)
        (Term.subst termSubst arguments)) :
    IsRenamingStableReducible
      ((Ty.effect operationSignature.resultCarrier effectTag).subst sigma)
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.effectPerform_isStronglyNormalizing
    (operationIsStable rhoIsInjective termRenaming)
    (Reducible.isStronglyNormalizing
      (argumentsAreStable rhoIsInjective termRenaming))


end LeanFX2
