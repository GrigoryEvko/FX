import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat/HoTT — typed compositional compat for HoTT ctors

Split from `Reduction/Compat.lean` (REFACTOR-COMPAT #1550) — keeps
the parent module under the 1000-line ceiling.

This module bundles the 7 per-ctor `Step.par.XCong.{rename,subst}_compatible`
theorems whose subjects are HoTT-layer term constructors:

* `oeqReflCong` — observational-equality reflexivity
* `oeqJCong` — observational J eliminator
* `oeqFunextCong` — pointwise-equality function extensionality
* `equivAppCong` — equivalence application
* `equivIntroCong` — equivalence introduction (forward + backward)
* `equivIntroHetCong` — heterogeneous equivalence intro
* `uaIntroHetCong` — heterogeneous univalence introduction

All zero-axiom under `#print axioms`.  Naming references via
`LeanFX2.Step.par.XCong.{rename,subst}_compatible` remain
namespace-stable across the split. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `oeqReflCong` (raw-witness inner premise).

Unlike `intervalOppCong`, the `oeqReflCong` constructor takes a
`RawStep.par` on the inner raw witness (not a typed `Step.par`),
because `Term.oeqRefl` carries an explicit `RawTerm` payload rather
than a typed sub-term.  The compositional shape is parallel: caller
supplies the renamed/substituted RAW step, this lemma packages it. -/
namespace oeqReflCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (renamedRawStep :
      RawStep.par (witnessRawSource.rename rho)
                  (witnessRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.oeqRefl (context := sourceCtx) carrier witnessRawSource))
      (Term.rename termRenaming
        (Term.oeqRefl (context := sourceCtx) carrier witnessRawTarget)) :=
  Step.par.oeqReflCong (carrier := carrier.rename rho) renamedRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (substitutedRawStep :
      RawStep.par (witnessRawSource.subst sigma.forRaw)
                  (witnessRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.oeqRefl (context := sourceCtx) carrier witnessRawSource))
      (Term.subst termSubst
        (Term.oeqRefl (context := sourceCtx) carrier witnessRawTarget)) :=
  Step.par.oeqReflCong (carrier := carrier.subst sigma) substitutedRawStep

end oeqReflCong

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

/-! ### `oeqJCong` (binary, base at motive + witness at oeq).

Binary exemplar with two inner Step.par premises: base at the
motive type, witness at the OEq type.  No mode hypothesis. -/
namespace oeqJCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget
     witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
        witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
        witnessRawTarget}
    (renamedBaseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (renamedWitnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming witnessTarget)) :
    Step.par
      (Term.rename termRenaming (Term.oeqJ baseSource witnessSource))
      (Term.rename termRenaming (Term.oeqJ baseTarget witnessTarget)) :=
  Step.par.oeqJCong renamedBaseStep renamedWitnessStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget
     witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
        witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
        witnessRawTarget}
    (substitutedBaseStep :
      Step.par (Term.subst termSubst baseSource)
               (Term.subst termSubst baseTarget))
    (substitutedWitnessStep :
      Step.par (Term.subst termSubst witnessSource)
               (Term.subst termSubst witnessTarget)) :
    Step.par
      (Term.subst termSubst (Term.oeqJ baseSource witnessSource))
      (Term.subst termSubst (Term.oeqJ baseTarget witnessTarget)) :=
  Step.par.oeqJCong substitutedBaseStep substitutedWitnessStep

end oeqJCong

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

/-! ### `uaIntroHetCong` (unary, heterogeneous univalence intro).

Unary exemplar with one inner Step.par premise on the
equivalence-witness term.  The witness's raw index is the
structured form `RawTerm.equivIntro forwardRaw backwardRaw`,
which renames/substitutes structurally via the corresponding
RawSubst equations, so the typed-Term step composes directly
through `Step.par.uaIntroHetCong`. -/
namespace uaIntroHetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {equivWitnessSource :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawSource backwardRawSource)}
    {equivWitnessTarget :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawTarget backwardRawTarget)}
    (renamedEquivWitnessStep :
      Step.par (Term.rename termRenaming equivWitnessSource)
               (Term.rename termRenaming equivWitnessTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessSource))
      (Term.rename termRenaming
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessTarget)) :=
  Step.par.uaIntroHetCong (context := targetCtx)
    innerLevel innerLevelLt
    (carrierARaw.rename rho) (carrierBRaw.rename rho)
    renamedEquivWitnessStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {equivWitnessSource :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawSource backwardRawSource)}
    {equivWitnessTarget :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawTarget backwardRawTarget)}
    (substitutedEquivWitnessStep :
      Step.par (Term.subst termSubst equivWitnessSource)
               (Term.subst termSubst equivWitnessTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessSource))
      (Term.subst termSubst
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessTarget)) :=
  Step.par.uaIntroHetCong (context := targetCtx)
    innerLevel innerLevelLt
    (carrierARaw.subst sigma.forRaw) (carrierBRaw.subst sigma.forRaw)
    substitutedEquivWitnessStep

end uaIntroHetCong

/-! ### `oeqFunextCong` (unary, pointwise-equality inner premise).

Unary cong rule with one inner Step.par premise on the
pointwise-equality function.  The pointwise type
`oeqFunextPointwiseType` is a computed Pi-type that does NOT
syntactically commute with `rename` / `subst` — Lean reports
a `▸` cast on the inner Term arguments.  We bridge by stating
the caller's premise at the renamed pointwise type using the
existing `oeqFunextPointwiseType_rename` / `_subst` commute
lemmas to align the type, then apply the cong constructor. -/
namespace oeqFunextCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRawSource pointwiseRawTarget : RawTerm sourceScope}
    {pointwiseSource :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRawSource}
    {pointwiseTarget :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRawTarget}
    (renamedPointwiseStep :
      Step.par
        (oeqFunextPointwiseType_rename rho
          domainType codomainType
          leftFunctionRaw rightFunctionRaw ▸
            Term.rename termRenaming pointwiseSource)
        (oeqFunextPointwiseType_rename rho
          domainType codomainType
          leftFunctionRaw rightFunctionRaw ▸
            Term.rename termRenaming pointwiseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseSource))
      (Term.rename termRenaming
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseTarget)) :=
  Step.par.oeqFunextCong (domainType.rename rho) (codomainType.rename rho)
    (leftFunctionRaw.rename rho) (rightFunctionRaw.rename rho)
    renamedPointwiseStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRawSource pointwiseRawTarget : RawTerm sourceScope}
    {pointwiseSource :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRawSource}
    {pointwiseTarget :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRawTarget}
    (substitutedPointwiseStep :
      Step.par
        (oeqFunextPointwiseType_subst sigma
          domainType codomainType
          leftFunctionRaw rightFunctionRaw ▸
            Term.subst termSubst pointwiseSource)
        (oeqFunextPointwiseType_subst sigma
          domainType codomainType
          leftFunctionRaw rightFunctionRaw ▸
            Term.subst termSubst pointwiseTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseSource))
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseTarget)) :=
  Step.par.oeqFunextCong (domainType.subst sigma) (codomainType.subst sigma)
    (leftFunctionRaw.subst sigma.forRaw) (rightFunctionRaw.subst sigma.forRaw)
    substitutedPointwiseStep

end oeqFunextCong

end par

end Step

end LeanFX2
