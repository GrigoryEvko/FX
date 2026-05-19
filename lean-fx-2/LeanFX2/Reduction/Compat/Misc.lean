import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat/Misc — typed compositional compat for misc ctors

Split from `Reduction/Compat.lean` (REFACTOR-COMPAT #1550) — keeps
the parent module under the 1000-line ceiling.

This module bundles the 5 per-ctor `Step.par.XCong.{rename,subst}_compatible`
theorems that don't fit cleanly into Cubical / HoTT / Effects:

* `cumulUpInnerCong` — universe cumulativity inner cong (CUMUL ladder)
* `recordProjCong` / `recordIntroCong` — single-field record proj/intro
* `idStrictReflCong` / `idStrictRecCong` — strict-id reflexivity / recursor

All zero-axiom under `#print axioms`.  Naming references via
`LeanFX2.Step.par.XCong.{rename,subst}_compatible` remain
namespace-stable across the split. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `cumulUpInnerCong` (unary, threads explicit cumul args). -/
namespace cumulUpInnerCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeSourceRaw codeTargetRaw : RawTerm sourceScope}
    {typeCodeSource :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming typeCodeSource)
               (Term.rename termRenaming typeCodeTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.cumulUp (context := sourceCtx)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeSource))
      (Term.rename termRenaming
        (Term.cumulUp (context := sourceCtx)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeTarget)) :=
  Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
    levelLeLow levelLeHigh renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeSourceRaw codeTargetRaw : RawTerm sourceScope}
    {typeCodeSource :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst typeCodeSource)
               (Term.subst termSubst typeCodeTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.cumulUp (context := sourceCtx)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeSource))
      (Term.subst termSubst
        (Term.cumulUp (context := sourceCtx)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeTarget)) :=
  Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
    levelLeLow levelLeHigh substitutedInnerStep

end cumulUpInnerCong

/-! ### `idStrictReflCong` (raw-witness inner premise, mode-strict gated).

Mirrors `oeqReflCong` exactly, but with the `modeIsStrict` mode-
discipline hypothesis threaded through (the `Term.idStrictRefl`
constructor requires `mode = Mode.strict`, unlike `Term.oeqRefl`
which is mode-polymorphic). -/
namespace idStrictReflCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (renamedRawStep :
      RawStep.par (witnessRawSource.rename rho)
                  (witnessRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict
          carrier witnessRawSource))
      (Term.rename termRenaming
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict
          carrier witnessRawTarget)) :=
  Step.par.idStrictReflCong (carrier := carrier.rename rho)
    modeIsStrict renamedRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (substitutedRawStep :
      RawStep.par (witnessRawSource.subst sigma.forRaw)
                  (witnessRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict
          carrier witnessRawSource))
      (Term.subst termSubst
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict
          carrier witnessRawTarget)) :=
  Step.par.idStrictReflCong (carrier := carrier.subst sigma)
    modeIsStrict substitutedRawStep

end idStrictReflCong

/-! ### `recordProjCong` (unary, single-field record projection).

Structurally identical to `intervalOppCong` — single inner Step.par
premise on a record-typed term, no mode hypothesis, no binder. -/
namespace recordProjCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {recordRawSource recordRawTarget : RawTerm sourceScope}
    {recordSource :
      Term sourceCtx (Ty.record singleFieldType) recordRawSource}
    {recordTarget :
      Term sourceCtx (Ty.record singleFieldType) recordRawTarget}
    (renamedRecordStep :
      Step.par (Term.rename termRenaming recordSource)
               (Term.rename termRenaming recordTarget)) :
    Step.par
      (Term.rename termRenaming (Term.recordProj recordSource))
      (Term.rename termRenaming (Term.recordProj recordTarget)) :=
  Step.par.recordProjCong renamedRecordStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {singleFieldType : Ty level sourceScope}
    {recordRawSource recordRawTarget : RawTerm sourceScope}
    {recordSource :
      Term sourceCtx (Ty.record singleFieldType) recordRawSource}
    {recordTarget :
      Term sourceCtx (Ty.record singleFieldType) recordRawTarget}
    (substitutedRecordStep :
      Step.par (Term.subst termSubst recordSource)
               (Term.subst termSubst recordTarget)) :
    Step.par
      (Term.subst termSubst (Term.recordProj recordSource))
      (Term.subst termSubst (Term.recordProj recordTarget)) :=
  Step.par.recordProjCong substitutedRecordStep

end recordProjCong

/-! ### `recordIntroCong` (unary, single-field record introduction).

Structurally identical to `recordProjCong` — single inner Step.par
premise on the field value, no mode hypothesis, no binder.  The
record's single field has type `singleFieldType`, and the typed
recordIntro produces a term at the matching `Ty.record`. -/
namespace recordIntroCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {firstRawSource firstRawTarget : RawTerm sourceScope}
    {firstSource : Term sourceCtx singleFieldType firstRawSource}
    {firstTarget : Term sourceCtx singleFieldType firstRawTarget}
    (renamedFirstStep :
      Step.par (Term.rename termRenaming firstSource)
               (Term.rename termRenaming firstTarget)) :
    Step.par
      (Term.rename termRenaming (Term.recordIntro firstSource))
      (Term.rename termRenaming (Term.recordIntro firstTarget)) :=
  Step.par.recordIntroCong renamedFirstStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {singleFieldType : Ty level sourceScope}
    {firstRawSource firstRawTarget : RawTerm sourceScope}
    {firstSource : Term sourceCtx singleFieldType firstRawSource}
    {firstTarget : Term sourceCtx singleFieldType firstRawTarget}
    (substitutedFirstStep :
      Step.par (Term.subst termSubst firstSource)
               (Term.subst termSubst firstTarget)) :
    Step.par
      (Term.subst termSubst (Term.recordIntro firstSource))
      (Term.subst termSubst (Term.recordIntro firstTarget)) :=
  Step.par.recordIntroCong substitutedFirstStep

end recordIntroCong

/-! ### `idStrictRecCong` (binary, mode-strict gated).

Binary exemplar with two inner Step.par premises: base at the
motive type, witness at the strict-id type.  Mode hypothesis
`mode = .strict`. -/
namespace idStrictRecCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget
     witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRawTarget}
    (renamedBaseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (renamedWitnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming witnessTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.idStrictRec modeIsStrict baseSource witnessSource))
      (Term.rename termRenaming
        (Term.idStrictRec modeIsStrict baseTarget witnessTarget)) :=
  Step.par.idStrictRecCong modeIsStrict renamedBaseStep renamedWitnessStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget
     witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRawTarget}
    (substitutedBaseStep :
      Step.par (Term.subst termSubst baseSource)
               (Term.subst termSubst baseTarget))
    (substitutedWitnessStep :
      Step.par (Term.subst termSubst witnessSource)
               (Term.subst termSubst witnessTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseSource witnessSource))
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseTarget witnessTarget)) :=
  Step.par.idStrictRecCong modeIsStrict substitutedBaseStep substitutedWitnessStep

end idStrictRecCong

end par

end Step

end LeanFX2
