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

#1590-CORE additions (2026-05-08): four canonical refl-fragment
funext / Id-witness ctors whose typed cong rules feed the
typed→raw bridge for Univalence/funext step rules:

* `reflCong` — Term.refl raw-witness-only (Id-types reflexivity)
* `funextReflCong` — canonical pointwise-refl funext (Pi/Id binder)
* `funextReflAtIdCong` — canonical Id-typed funext at arrow types
* `funextIntroHetCong` — heterogeneous-carrier funext-introduction

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

/-! ### `reflCong` (Id-types reflexivity, raw-witness inner premise).

`Term.refl carrier rawWitness : Term context (Ty.id carrier rawWitness
rawWitness) (RawTerm.refl rawWitness)`.  The `Step.par.reflCong`
constructor takes a `RawStep.par` on the inner raw witness; the typed
source/target Ty differ in their endpoint raws, which Step.par's
heterogeneous typing accommodates.

Per `Term.rename` (line 287), `Term.rename termRenaming (Term.refl
carrier rawWitness) = Term.refl (carrier.rename rho) (rawWitness.rename
rho)` definitionally — so the renamed/substituted endpoints align via
the carrier-renamed shape, and the proof reduces to applying the
constructor with the carrier transported. -/
namespace reflCong

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
        (Term.refl (context := sourceCtx) carrier witnessRawSource))
      (Term.rename termRenaming
        (Term.refl (context := sourceCtx) carrier witnessRawTarget)) :=
  Step.par.reflCong (carrier := carrier.rename rho) renamedRawStep

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
        (Term.refl (context := sourceCtx) carrier witnessRawSource))
      (Term.subst termSubst
        (Term.refl (context := sourceCtx) carrier witnessRawTarget)) :=
  Step.par.reflCong (carrier := carrier.subst sigma) substitutedRawStep

end reflCong

/-! ### `funextReflCong` (canonical pointwise-refl funext).

`Term.funextRefl domainType codomainType applyRaw` has Ty
`Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)`
and raw form `RawTerm.lam (RawTerm.refl applyRaw)` at scope+1.

The rename arm in `Term/Rename.lean` returns `codomainEqInverse ▸
Term.funextRefl (domainType.rename rho) (codomainType.rename rho)
(applyRaw.rename rho.lift)` where `codomainEqInverse :
(codomainType.rename rho).weaken = codomainType.weaken.rename rho.lift`
is `(Ty.weaken_rename_commute rho codomainType).symm`.

The cast wraps the WHOLE Term (not just an inner subterm).  We bridge
by using the SAME `codomainEqInverse` to transport the
`Step.par.funextReflCong` proof on the un-cast un-renamed-codomain
side to the post-cast Ty index.  Since Step.par is fully heterogeneous
in its source/target Ty, the same `Step.par.funextReflCong` builds
either side; the cast on the proof simply realigns the dependent
contexts. -/
namespace funextReflCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (renamedApplyRawStep :
      RawStep.par (applyRawSource.rename rho.lift)
                  (applyRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawSource))
      (Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawTarget)) :=
  -- Per `Term.rename`'s funextRefl arm (`Term/Rename.lean:441-454`),
  -- both Terms unfold to `(Ty.weaken_rename_commute rho codomainType).symm
  -- ▸ Term.funextRefl (domainType.rename rho) (codomainType.rename rho)
  -- (applyRaw.rename rho.lift)`.  We use Eq.rec on the symmetric
  -- equality `commuteSymmEq : (codomainType.rename rho).weaken =
  -- codomainType.weaken.rename rho.lift` with a motive `weakRenamedCo
  -- ↦ Step.par (eqProof ▸ Term.funextRefl ... weakRenamedCo ...) (...)`.
  -- The variable `weakRenamedCo` is the LHS of the equality, which
  -- appears (definitionally) as `(codomainType.rename rho).weaken`
  -- inside the un-cast Term.funextRefl's Ty index.  At the rfl
  -- branch, `eqProof = rfl` and the cast vanishes; the constructor
  -- closes the goal directly.
  let commuteSymm :
      (codomainType.rename rho).weaken =
        codomainType.weaken.rename rho.lift :=
    (Ty.weaken_rename_commute rho codomainType).symm
  @Eq.rec (Ty level (targetScope + 1))
    ((codomainType.rename rho).weaken)
    (motive := fun (weakRenamedCodomain : Ty level (targetScope + 1))
      (eqProof : (codomainType.rename rho).weaken = weakRenamedCodomain) =>
      Step.par
        (eqProof ▸
          Term.funextRefl (context := targetCtx)
            (domainType.rename rho) (codomainType.rename rho)
            (applyRawSource.rename rho.lift))
        (eqProof ▸
          Term.funextRefl (context := targetCtx)
            (domainType.rename rho) (codomainType.rename rho)
            (applyRawTarget.rename rho.lift)))
    (Step.par.funextReflCong (domainType.rename rho)
                             (codomainType.rename rho)
                             renamedApplyRawStep)
    (codomainType.weaken.rename rho.lift)
    commuteSymm

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (substitutedApplyRawStep :
      RawStep.par (applyRawSource.subst sigma.forRaw.lift)
                  (applyRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawSource))
      (Term.subst termSubst
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawTarget)) :=
  -- Mirror of `rename_compatible`: the substituted Terms unfold to
  -- `codomainEqInverse ▸ Term.funextRefl ...` per `Term/Subst.lean`'s
  -- funextRefl arm (lines 422-436).  Bridge via Eq.rec over the
  -- symmetric equality with motive lifting both source/target casts.
  let commuteSymm :
      (codomainType.subst sigma).weaken =
        codomainType.weaken.subst sigma.lift :=
    (Ty.weaken_subst_commute sigma codomainType).symm
  @Eq.rec (Ty level (targetScope + 1))
    ((codomainType.subst sigma).weaken)
    (motive := fun (weakSubstCodomain : Ty level (targetScope + 1))
      (eqProof : (codomainType.subst sigma).weaken = weakSubstCodomain) =>
      Step.par
        (eqProof ▸
          Term.funextRefl (context := targetCtx)
            (domainType.subst sigma) (codomainType.subst sigma)
            (applyRawSource.subst sigma.forRaw.lift))
        (eqProof ▸
          Term.funextRefl (context := targetCtx)
            (domainType.subst sigma) (codomainType.subst sigma)
            (applyRawTarget.subst sigma.forRaw.lift)))
    (Step.par.funextReflCong (domainType.subst sigma)
                             (codomainType.subst sigma)
                             substitutedApplyRawStep)
    (codomainType.weaken.subst sigma.lift)
    commuteSymm

end funextReflCong

/-! ### `funextReflAtIdCong` (canonical Id-typed funext at arrow types).

Mirror of `funextReflCong` at the Id-typed shape: `Term.funextReflAtId
domainType codomainType applyRaw` has Ty
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam (RawTerm.refl
applyRaw)) (RawTerm.lam (RawTerm.refl applyRaw))`.  Unlike
`funextReflCong`, no `Ty.weaken_*_commute` cast is needed because
`Ty.id` and `Ty.arrow` are non-binder carriers whose substitution
doesn't introduce a scope shift.  The applyRaw at scope+1 lifts via
`rho.lift` / `sigma.forRaw.lift`. -/
namespace funextReflAtIdCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (renamedApplyRawStep :
      RawStep.par (applyRawSource.rename rho.lift)
                  (applyRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawSource))
      (Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawTarget)) :=
  Step.par.funextReflAtIdCong (domainType.rename rho)
                              (codomainType.rename rho)
                              renamedApplyRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (substitutedApplyRawStep :
      RawStep.par (applyRawSource.subst sigma.forRaw.lift)
                  (applyRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawSource))
      (Term.subst termSubst
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawTarget)) :=
  Step.par.funextReflAtIdCong (domainType.subst sigma)
                              (codomainType.subst sigma)
                              substitutedApplyRawStep

end funextReflAtIdCong

/-! ### `funextIntroHetCong` (heterogeneous-carrier funext-introduction).

`Term.funextIntroHet domainType codomainType applyARaw applyBRaw`
has Ty `Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam
applyARaw) (RawTerm.lam applyBRaw)` and raw form `RawTerm.lam
(RawTerm.refl applyARaw)`.  The constructor stores both `applyARaw`
and `applyBRaw` at scope+1; the `Step.par.funextIntroHetCong` rule
takes TWO `RawStep.par` premises (one per applyRaw).  Like
`funextReflAtIdCong`, no `Ty.weaken_*_commute` cast is needed —
`Ty.id` / `Ty.arrow` are non-binder carriers. -/
namespace funextIntroHetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyARawSource applyARawTarget applyBRawSource applyBRawTarget :
      RawTerm (sourceScope + 1)}
    (renamedApplyARawStep :
      RawStep.par (applyARawSource.rename rho.lift)
                  (applyARawTarget.rename rho.lift))
    (renamedApplyBRawStep :
      RawStep.par (applyBRawSource.rename rho.lift)
                  (applyBRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawSource applyBRawSource))
      (Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawTarget applyBRawTarget)) :=
  Step.par.funextIntroHetCong (domainType.rename rho)
                              (codomainType.rename rho)
                              renamedApplyARawStep renamedApplyBRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyARawSource applyARawTarget applyBRawSource applyBRawTarget :
      RawTerm (sourceScope + 1)}
    (substitutedApplyARawStep :
      RawStep.par (applyARawSource.subst sigma.forRaw.lift)
                  (applyARawTarget.subst sigma.forRaw.lift))
    (substitutedApplyBRawStep :
      RawStep.par (applyBRawSource.subst sigma.forRaw.lift)
                  (applyBRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawSource applyBRawSource))
      (Term.subst termSubst
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawTarget applyBRawTarget)) :=
  Step.par.funextIntroHetCong (domainType.subst sigma)
                              (codomainType.subst sigma)
                              substitutedApplyARawStep
                              substitutedApplyBRawStep

end funextIntroHetCong

end par

end Step

end LeanFX2
