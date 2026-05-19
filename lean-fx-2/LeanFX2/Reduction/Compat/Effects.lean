import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat/Effects — typed compositional compat for effect-system ctors

Split from `Reduction/Compat.lean` (REFACTOR-COMPAT #1550) — keeps
the parent module under the 1000-line ceiling.

This module bundles the 7 per-ctor `Step.par.XCong.{rename,subst}_compatible`
theorems whose subjects are effect-system / refinement / codata /
session term constructors:

* `refineElimCong` / `refineIntroCong` — refinement-type elim/intro
* `codataDestCong` / `codataUnfoldCong` — codata destructor / unfold
* `sessionRecvCong` / `sessionSendCong` — session protocol recv/send
* `effectPerformCong` — algebraic-effect perform

All zero-axiom under `#print axioms`.  Naming references via
`LeanFX2.Step.par.XCong.{rename,subst}_compatible` remain
namespace-stable across the split. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `refineElimCong` (unary). -/
namespace refineElimCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRawSource refinedRawTarget : RawTerm sourceScope}
    {refinedSource :
      Term sourceCtx (Ty.refine baseType predicate) refinedRawSource}
    {refinedTarget :
      Term sourceCtx (Ty.refine baseType predicate) refinedRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming refinedSource)
               (Term.rename termRenaming refinedTarget)) :
    Step.par
      (Term.rename termRenaming (Term.refineElim refinedSource))
      (Term.rename termRenaming (Term.refineElim refinedTarget)) :=
  Step.par.refineElimCong renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRawSource refinedRawTarget : RawTerm sourceScope}
    {refinedSource :
      Term sourceCtx (Ty.refine baseType predicate) refinedRawSource}
    {refinedTarget :
      Term sourceCtx (Ty.refine baseType predicate) refinedRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst refinedSource)
               (Term.subst termSubst refinedTarget)) :
    Step.par
      (Term.subst termSubst (Term.refineElim refinedSource))
      (Term.subst termSubst (Term.refineElim refinedTarget)) :=
  Step.par.refineElimCong substitutedInnerStep

end refineElimCong

/-! ### `codataDestCong` (unary). -/
namespace codataDestCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {codataRawSource codataRawTarget : RawTerm sourceScope}
    {codataSource :
      Term sourceCtx (Ty.codata stateType outputType) codataRawSource}
    {codataTarget :
      Term sourceCtx (Ty.codata stateType outputType) codataRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming codataSource)
               (Term.rename termRenaming codataTarget)) :
    Step.par
      (Term.rename termRenaming (Term.codataDest codataSource))
      (Term.rename termRenaming (Term.codataDest codataTarget)) :=
  Step.par.codataDestCong renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {stateType outputType : Ty level sourceScope}
    {codataRawSource codataRawTarget : RawTerm sourceScope}
    {codataSource :
      Term sourceCtx (Ty.codata stateType outputType) codataRawSource}
    {codataTarget :
      Term sourceCtx (Ty.codata stateType outputType) codataRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst codataSource)
               (Term.subst termSubst codataTarget)) :
    Step.par
      (Term.subst termSubst (Term.codataDest codataSource))
      (Term.subst termSubst (Term.codataDest codataTarget)) :=
  Step.par.codataDestCong substitutedInnerStep

end codataDestCong

/-! ### `sessionRecvCong` (unary). -/
namespace sessionRecvCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {protocolStep : RawTerm sourceScope}
    {channelRawSource channelRawTarget : RawTerm sourceScope}
    {channelSource :
      Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget :
      Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming channelSource)
               (Term.rename termRenaming channelTarget)) :
    Step.par
      (Term.rename termRenaming (Term.sessionRecv channelSource))
      (Term.rename termRenaming (Term.sessionRecv channelTarget)) :=
  Step.par.sessionRecvCong renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {protocolStep : RawTerm sourceScope}
    {channelRawSource channelRawTarget : RawTerm sourceScope}
    {channelSource :
      Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget :
      Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst channelSource)
               (Term.subst termSubst channelTarget)) :
    Step.par
      (Term.subst termSubst (Term.sessionRecv channelSource))
      (Term.subst termSubst (Term.sessionRecv channelTarget)) :=
  Step.par.sessionRecvCong substitutedInnerStep

end sessionRecvCong

/-! ### `effectPerformCong` (binary). -/
namespace effectPerformCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level sourceScope)}
    {canPerformOperation :
      Effects.CanPerform effectRow operationSignature}
    {operationRawSource operationRawTarget
     argumentsRawSource argumentsRawTarget : RawTerm sourceScope}
    {operationSource :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRawSource}
    {operationTarget :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRawTarget}
    {argumentsSource :
      Term sourceCtx operationSignature.argumentCarrier argumentsRawSource}
    {argumentsTarget :
      Term sourceCtx operationSignature.argumentCarrier argumentsRawTarget}
    (renamedOperationStep :
      Step.par (Term.rename termRenaming operationSource)
               (Term.rename termRenaming operationTarget))
    (renamedArgumentsStep :
      Step.par (Term.rename termRenaming argumentsSource)
               (Term.rename termRenaming argumentsTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationSource argumentsSource))
      (Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTarget argumentsTarget)) :=
  Step.par.effectPerformCong renamedOperationStep renamedArgumentsStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level sourceScope)}
    {canPerformOperation :
      Effects.CanPerform effectRow operationSignature}
    {operationRawSource operationRawTarget
     argumentsRawSource argumentsRawTarget : RawTerm sourceScope}
    {operationSource :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRawSource}
    {operationTarget :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRawTarget}
    {argumentsSource :
      Term sourceCtx operationSignature.argumentCarrier argumentsRawSource}
    {argumentsTarget :
      Term sourceCtx operationSignature.argumentCarrier argumentsRawTarget}
    (substitutedOperationStep :
      Step.par (Term.subst termSubst operationSource)
               (Term.subst termSubst operationTarget))
    (substitutedArgumentsStep :
      Step.par (Term.subst termSubst argumentsSource)
               (Term.subst termSubst argumentsTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationSource argumentsSource))
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTarget argumentsTarget)) :=
  Step.par.effectPerformCong substitutedOperationStep substitutedArgumentsStep

end effectPerformCong

/-! ### `sessionSendCong` (binary). -/
namespace sessionSendCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {protocolStep : RawTerm sourceScope}
    {payloadType : Ty level sourceScope}
    {channelRawSource channelRawTarget payloadRawSource payloadRawTarget :
      RawTerm sourceScope}
    {channelSource : Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget : Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    {payloadSource : Term sourceCtx payloadType payloadRawSource}
    {payloadTarget : Term sourceCtx payloadType payloadRawTarget}
    (renamedChannelStep :
      Step.par (Term.rename termRenaming channelSource)
               (Term.rename termRenaming channelTarget))
    (renamedPayloadStep :
      Step.par (Term.rename termRenaming payloadSource)
               (Term.rename termRenaming payloadTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.sessionSend protocolStep channelSource payloadSource))
      (Term.rename termRenaming
        (Term.sessionSend protocolStep channelTarget payloadTarget)) :=
  Step.par.sessionSendCong renamedChannelStep renamedPayloadStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {protocolStep : RawTerm sourceScope}
    {payloadType : Ty level sourceScope}
    {channelRawSource channelRawTarget payloadRawSource payloadRawTarget :
      RawTerm sourceScope}
    {channelSource : Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget : Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    {payloadSource : Term sourceCtx payloadType payloadRawSource}
    {payloadTarget : Term sourceCtx payloadType payloadRawTarget}
    (substitutedChannelStep :
      Step.par (Term.subst termSubst channelSource)
               (Term.subst termSubst channelTarget))
    (substitutedPayloadStep :
      Step.par (Term.subst termSubst payloadSource)
               (Term.subst termSubst payloadTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.sessionSend protocolStep channelSource payloadSource))
      (Term.subst termSubst
        (Term.sessionSend protocolStep channelTarget payloadTarget)) :=
  Step.par.sessionSendCong substitutedChannelStep substitutedPayloadStep

end sessionSendCong

/-! ### `refineIntroCong` (binary, value at base + proof at unit).

Structurally a binary exemplar: two inner Step.par premises (one
on the value at `baseType`, one on the proof witness at
`Ty.unit`).  No mode hypothesis.  The shared `predicate` term
on `RawTerm (scope + 1)` is index data, not a step subject. -/
namespace refineIntroCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRawSource valueRawTarget proofRawSource proofRawTarget :
      RawTerm sourceScope}
    {valueSource : Term sourceCtx baseType valueRawSource}
    {valueTarget : Term sourceCtx baseType valueRawTarget}
    {proofSource : Term sourceCtx Ty.unit proofRawSource}
    {proofTarget : Term sourceCtx Ty.unit proofRawTarget}
    (renamedValueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (renamedProofStep :
      Step.par (Term.rename termRenaming proofSource)
               (Term.rename termRenaming proofTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.refineIntro predicate valueSource proofSource))
      (Term.rename termRenaming
        (Term.refineIntro predicate valueTarget proofTarget)) :=
  Step.par.refineIntroCong renamedValueStep renamedProofStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRawSource valueRawTarget proofRawSource proofRawTarget :
      RawTerm sourceScope}
    {valueSource : Term sourceCtx baseType valueRawSource}
    {valueTarget : Term sourceCtx baseType valueRawTarget}
    {proofSource : Term sourceCtx Ty.unit proofRawSource}
    {proofTarget : Term sourceCtx Ty.unit proofRawTarget}
    (substitutedValueStep :
      Step.par (Term.subst termSubst valueSource)
               (Term.subst termSubst valueTarget))
    (substitutedProofStep :
      Step.par (Term.subst termSubst proofSource)
               (Term.subst termSubst proofTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.refineIntro predicate valueSource proofSource))
      (Term.subst termSubst
        (Term.refineIntro predicate valueTarget proofTarget)) :=
  Step.par.refineIntroCong substitutedValueStep substitutedProofStep

end refineIntroCong

/-! ### `codataUnfoldCong` (binary, state + transition function).

Binary exemplar with two inner Step.par premises: one on the
state at `stateType`, one on the transition function at
`Ty.arrow stateType outputType`.  No mode hypothesis. -/
namespace codataUnfoldCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {stateRawSource stateRawTarget transitionRawSource transitionRawTarget :
      RawTerm sourceScope}
    {stateSource : Term sourceCtx stateType stateRawSource}
    {stateTarget : Term sourceCtx stateType stateRawTarget}
    {transitionSource :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawSource}
    {transitionTarget :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawTarget}
    (renamedStateStep :
      Step.par (Term.rename termRenaming stateSource)
               (Term.rename termRenaming stateTarget))
    (renamedTransitionStep :
      Step.par (Term.rename termRenaming transitionSource)
               (Term.rename termRenaming transitionTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.codataUnfold stateSource transitionSource))
      (Term.rename termRenaming
        (Term.codataUnfold stateTarget transitionTarget)) :=
  Step.par.codataUnfoldCong renamedStateStep renamedTransitionStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {stateType outputType : Ty level sourceScope}
    {stateRawSource stateRawTarget transitionRawSource transitionRawTarget :
      RawTerm sourceScope}
    {stateSource : Term sourceCtx stateType stateRawSource}
    {stateTarget : Term sourceCtx stateType stateRawTarget}
    {transitionSource :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawSource}
    {transitionTarget :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawTarget}
    (substitutedStateStep :
      Step.par (Term.subst termSubst stateSource)
               (Term.subst termSubst stateTarget))
    (substitutedTransitionStep :
      Step.par (Term.subst termSubst transitionSource)
               (Term.subst termSubst transitionTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.codataUnfold stateSource transitionSource))
      (Term.subst termSubst
        (Term.codataUnfold stateTarget transitionTarget)) :=
  Step.par.codataUnfoldCong substitutedStateStep substitutedTransitionStep

end codataUnfoldCong

end par

end Step

end LeanFX2
