import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # LeanFX2.Reduction.Compat.HoTT.EquivalenceFamily

Typed compositional `rename`/`subst` compat lemmas for the
equivalence family of HoTT cong constructors:

* `equivAppCong` — equivalence application (binary)
* `equivIntroCong` — equivalence introduction (forward + backward)
* `equivIntroHetCong` — heterogeneous equivalence intro (alias of
  `equivIntroCong` at the constructor catalog level)

Split from `LeanFX2/Reduction/Compat/HoTT.lean` (REFACTOR-COMPAT
#1556) — keeps the parent module under the 1000-line ceiling.

## Root status

Layer 2 reduction-compat HoTT helper.  All declarations remain
zero-axiom under `#print axioms` and preserve their original
fully-qualified namespace `LeanFX2.Step.par.XCong.{rename,subst}_compatible`. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `equivAppCong` (binary). -/
namespace equivAppCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget argumentRawSource argumentRawTarget :
      RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (renamedEquivStep :
      Step.par (Term.rename termRenaming equivSource)
               (Term.rename termRenaming equivTarget))
    (renamedArgumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.equivApp equivSource argumentSource))
      (Term.rename termRenaming (Term.equivApp equivTarget argumentTarget)) :=
  Step.par.equivAppCong renamedEquivStep renamedArgumentStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget argumentRawSource argumentRawTarget :
      RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (substitutedEquivStep :
      Step.par (Term.subst termSubst equivSource)
               (Term.subst termSubst equivTarget))
    (substitutedArgumentStep :
      Step.par (Term.subst termSubst argumentSource)
               (Term.subst termSubst argumentTarget)) :
    Step.par
      (Term.subst termSubst (Term.equivApp equivSource argumentSource))
      (Term.subst termSubst (Term.equivApp equivTarget argumentTarget)) :=
  Step.par.equivAppCong substitutedEquivStep substitutedArgumentStep

end equivAppCong

/-! ### `equivIntroCong` (binary, equivalence-intro with leftInv/rightInv data).

Binary exemplar: two inner Step.par premises (forward + backward),
plus heterogeneous leftInv/rightInv typed data carrying the source
and target inverse-witness raw forms.  No mode hypothesis. -/
namespace equivIntroCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (renamedForwardStep :
      Step.par (Term.rename termRenaming forwardSource)
               (Term.rename termRenaming forwardTarget))
    (renamedBackwardStep :
      Step.par (Term.rename termRenaming backwardSource)
               (Term.rename termRenaming backwardTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.rename termRenaming
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) :=
  Step.par.equivIntroCong renamedForwardStep renamedBackwardStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (substitutedForwardStep :
      Step.par (Term.subst termSubst forwardSource)
               (Term.subst termSubst forwardTarget))
    (substitutedBackwardStep :
      Step.par (Term.subst termSubst backwardSource)
               (Term.subst termSubst backwardTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.subst termSubst
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) :=
  Step.par.equivIntroCong substitutedForwardStep substitutedBackwardStep

end equivIntroCong

/-! ### `equivIntroHetCong` (alias of `equivIntroCong`, same shape).

Identical signature to `equivIntroCong` — both produce
`Term.equivIntroHet` from forward + backward typed steps.  Kept
as a separate namespace for headline parity with the constructor
catalog. -/
namespace equivIntroHetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (renamedForwardStep :
      Step.par (Term.rename termRenaming forwardSource)
               (Term.rename termRenaming forwardTarget))
    (renamedBackwardStep :
      Step.par (Term.rename termRenaming backwardSource)
               (Term.rename termRenaming backwardTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.rename termRenaming
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) :=
  Step.par.equivIntroHetCong renamedForwardStep renamedBackwardStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (substitutedForwardStep :
      Step.par (Term.subst termSubst forwardSource)
               (Term.subst termSubst forwardTarget))
    (substitutedBackwardStep :
      Step.par (Term.subst termSubst backwardSource)
               (Term.subst termSubst backwardTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.subst termSubst
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) :=
  Step.par.equivIntroHetCong substitutedForwardStep substitutedBackwardStep

end equivIntroHetCong

end par

end Step

end LeanFX2
