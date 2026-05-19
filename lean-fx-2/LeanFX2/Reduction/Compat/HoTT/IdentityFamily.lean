import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # LeanFX2.Reduction.Compat.HoTT.IdentityFamily

Typed compositional `rename`/`subst` compat lemmas for the
identity-type / observational-equality family of HoTT cong
constructors:

* `oeqReflCong` — observational-equality reflexivity (raw witness)
* `oeqJCong` — observational J eliminator (binary)
* `oeqFunextCong` — pointwise-equality function extensionality
* `reflCong` — Id-types reflexivity (raw witness)

Split from `LeanFX2/Reduction/Compat/HoTT.lean` (REFACTOR-COMPAT
#1556) — keeps the parent module under the 1000-line ceiling.

## Root status

Layer 2 reduction-compat HoTT helper.  All declarations remain
zero-axiom under `#print axioms` and preserve their original
fully-qualified namespace `LeanFX2.Step.par.XCong.{rename,subst}_compatible`. -/

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

end par

end Step

end LeanFX2
