import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat — rename + subst compatibility

Renaming and substitution preserve every reduction relation:
* `Step` (single step)
* `Step.par` (parallel reduction)
* `StepStar` (multi-step) — via `mapStep`
* `Conv` (definitional conversion) — via `mapStep`

## The big simplification (from lean-fx)

In lean-fx, β-arms required a separate `RawConsistent` hypothesis
threaded through ~17 files because `Term.subst0_term` consulted the
raw side via a `forRaw` field that could be inconsistent with the
typed `forTy`.  In lean-fx-2, `RawTerm scope` is a Term type-level
index — every typed Term is automatically raw-consistent — so no
threading is needed.  Subst-compat proofs are ~30% smaller.

## Shipped slice

This module currently carries the raw-layer compatibility API that the typed
bridge and confluence layers consume.  It deliberately stays in Layer 2 and
therefore does not import the later `LeanFX2.Bridge` module.

The still-missing typed endpoint theorem

```lean
Step.par (source.rename rho) (target.rename rho)
```

has to thread the dependent casts produced by `Term.rename` / `Term.subst`
through every beta and eliminator arm.  That remains a separate Day-2
obligation; the declarations below are honest raw-level compatibility names
over the already-proved raw induction theorems.

## D2.10 typed compositional compat (per-cong)

The per-cong typed compat lemmas ship as compositional theorems: each
takes the renamed/substituted inner Step.par as a HYPOTHESIS and
produces the outer Step.par by applying the corresponding cong
constructor.  This pattern avoids needing a typed
`Step.par.rename` / `Step.par.subst` induction theorem (which would
require ~500 LoC of dep-cast threading).  The compositional
approach lets confluence consumers obtain the per-cong compat by
combining the inner-step compat (proved separately) with these
single-rule combinators.

## Remaining phase plan

* Step 1 (cong-only Step.rename_compatible) — port all ~30 cong
  cases first, keeping β/ι behind helper lemmas.
* Step 2 (Term.rename_subst0_HEq) — the subst-rename commute lemma
  at the typed-Term level, needed for β cases.
* Step 3 (β/ι cases of Step.rename_compatible).
* Step 4 (Step.subst_compatible) — mirror via TermSubst.
* Step 5 (Step.par.rename_compatible / subst_compatible).
* Step 6 (StepStar / Conv corollaries via mapStep).
-/

namespace LeanFX2

namespace RawStep

namespace par

/-- Compatibility name for raw parallel reduction under renaming.

This is a thin, audited API wrapper around `RawStep.par.rename`; keeping it in
`Reduction/Compat.lean` gives downstream code a stable import that names the
compatibility obligation directly. -/
theorem rename_compatible {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.rename rawRenaming)
                (afterTerm.rename rawRenaming) :=
  RawStep.par.rename rawRenaming parallelStep

/-- Compatibility name for raw parallel reduction under two pointwise-related
substitutions.

This is the general joint-substitution theorem already proved by induction in
`RawParCompatible.lean`, re-exported here under the Day-2 compatibility API. -/
theorem subst_compatible {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst firstSubst)
                (afterTerm.subst secondSubst) :=
  RawStep.par.subst_par substsRelated parallelStep

/-- Same-substitution corollary of `subst_compatible`. -/
theorem subst_compatible_same {sourceScope targetScope : Nat}
    (rawSubst : RawTermSubst sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst rawSubst)
                (afterTerm.subst rawSubst) :=
  RawStep.par.subst_compatible
    (fun position => RawStep.par.refl (rawSubst position))
    parallelStep

end par

end RawStep

/-! ## D2.10 typed compositional compat — exemplar `intervalOppCong`. -/

namespace Step

namespace par

namespace intervalOppCong

/-- Compositional typed rename-compat for `Step.par.intervalOppCong`.

Given a typed renaming and a Step.par on the inner interval values
that has ALREADY been transported across the renaming, produce the
parent `Step.par` on `Term.intervalOpp ...` after renaming.

The proof reduces to applying the `intervalOppCong` constructor
because `Term.rename` on `Term.intervalOpp innerValue` unfolds to
`Term.intervalOpp (Term.rename termRenaming innerValue)`, and
`Ty.interval.rename rho = Ty.interval` is `rfl`.

Compositional pattern (option (a) in D2.10): the caller supplies the
renamed-inner Step.par as a hypothesis; this lemma packages it into
the outer Step.par.  No typed induction principle for `Step.par`
is required — the toolkit-style API is sufficient for confluence
consumers, which build inner Step.pars first and aggregate via
these combinators. -/
theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx Ty.interval innerRawSource}
    {innerTarget : Term sourceCtx Ty.interval innerRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalOpp innerSource))
      (Term.rename termRenaming (Term.intervalOpp innerTarget)) :=
  Step.par.intervalOppCong renamedInnerStep

/-- Compositional typed subst-compat for `Step.par.intervalOppCong`.

Mirror of `rename_compatible` for `Term.subst`.  Given a typed
substitution and a Step.par on the inner interval values that has
ALREADY been transported across the substitution, produce the
parent `Step.par` on `Term.intervalOpp ...` after substitution.

Note: there is only ONE substituted Step.par hypothesis (no
"pointwise-related substs" yet) — the simplest compositional shape.
A future variant for the pointwise-related-substs case (mirror of
`RawStep.par.subst_compatible`) can be added once subst-pointwise
infrastructure is in place at the typed level. -/
theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx Ty.interval innerRawSource}
    {innerTarget : Term sourceCtx Ty.interval innerRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst innerSource)
               (Term.subst termSubst innerTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalOpp innerSource))
      (Term.subst termSubst (Term.intervalOpp innerTarget)) :=
  Step.par.intervalOppCong substitutedInnerStep

end intervalOppCong

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

/-! ### `glueElimCong` (unary, mode-univalent gated). -/
namespace glueElimCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming gluedSource)
               (Term.rename termRenaming gluedTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.glueElim modeIsUnivalent gluedSource))
      (Term.rename termRenaming
        (Term.glueElim modeIsUnivalent gluedTarget)) :=
  Step.par.glueElimCong modeIsUnivalent renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst gluedSource)
               (Term.subst termSubst gluedTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedSource))
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedTarget)) :=
  Step.par.glueElimCong modeIsUnivalent substitutedInnerStep

end glueElimCong

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

/-! ### `intervalMeetCong` (binary, both inners at `Ty.interval`). -/
namespace intervalMeetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (renamedLeftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (renamedRightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalMeet leftSource rightSource))
      (Term.rename termRenaming (Term.intervalMeet leftTarget rightTarget)) :=
  Step.par.intervalMeetCong renamedLeftStep renamedRightStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (substitutedLeftStep :
      Step.par (Term.subst termSubst leftSource)
               (Term.subst termSubst leftTarget))
    (substitutedRightStep :
      Step.par (Term.subst termSubst rightSource)
               (Term.subst termSubst rightTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalMeet leftSource rightSource))
      (Term.subst termSubst (Term.intervalMeet leftTarget rightTarget)) :=
  Step.par.intervalMeetCong substitutedLeftStep substitutedRightStep

end intervalMeetCong

/-! ### `intervalJoinCong` (binary, both inners at `Ty.interval`). -/
namespace intervalJoinCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (renamedLeftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (renamedRightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalJoin leftSource rightSource))
      (Term.rename termRenaming (Term.intervalJoin leftTarget rightTarget)) :=
  Step.par.intervalJoinCong renamedLeftStep renamedRightStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (substitutedLeftStep :
      Step.par (Term.subst termSubst leftSource)
               (Term.subst termSubst leftTarget))
    (substitutedRightStep :
      Step.par (Term.subst termSubst rightSource)
               (Term.subst termSubst rightTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalJoin leftSource rightSource))
      (Term.subst termSubst (Term.intervalJoin leftTarget rightTarget)) :=
  Step.par.intervalJoinCong substitutedLeftStep substitutedRightStep

end intervalJoinCong

/-! ### `pathAppCong` (binary, mode-univalent gated). -/
namespace pathAppCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
      RawTerm sourceScope}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (renamedPathStep :
      Step.par (Term.rename termRenaming pathSource)
               (Term.rename termRenaming pathTarget))
    (renamedIntervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent pathTarget intervalTarget)) :=
  Step.par.pathAppCong modeIsUnivalent renamedPathStep renamedIntervalStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
      RawTerm sourceScope}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (substitutedPathStep :
      Step.par (Term.subst termSubst pathSource)
               (Term.subst termSubst pathTarget))
    (substitutedIntervalStep :
      Step.par (Term.subst termSubst intervalSource)
               (Term.subst termSubst intervalTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathTarget intervalTarget)) :=
  Step.par.pathAppCong modeIsUnivalent substitutedPathStep substitutedIntervalStep

end pathAppCong

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

/-! ### `hcompCong` (binary, mode-univalent gated, both at carrier).

Binary exemplar: two inner Step.par premises (sides + cap), both
at the shared `carrierType`.  Mode hypothesis `mode = .univalent`
threaded through. -/
namespace hcompCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesSource : Term sourceCtx carrierType sidesRawSource}
    {sidesTarget : Term sourceCtx carrierType sidesRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (renamedSidesStep :
      Step.par (Term.rename termRenaming sidesSource)
               (Term.rename termRenaming sidesTarget))
    (renamedCapStep :
      Step.par (Term.rename termRenaming capSource)
               (Term.rename termRenaming capTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcomp modeIsUnivalent sidesSource capSource))
      (Term.rename termRenaming
        (Term.hcomp modeIsUnivalent sidesTarget capTarget)) :=
  Step.par.hcompCong modeIsUnivalent renamedSidesStep renamedCapStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesSource : Term sourceCtx carrierType sidesRawSource}
    {sidesTarget : Term sourceCtx carrierType sidesRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (substitutedSidesStep :
      Step.par (Term.subst termSubst sidesSource)
               (Term.subst termSubst sidesTarget))
    (substitutedCapStep :
      Step.par (Term.subst termSubst capSource)
               (Term.subst termSubst capTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.hcomp modeIsUnivalent sidesSource capSource))
      (Term.subst termSubst
        (Term.hcomp modeIsUnivalent sidesTarget capTarget)) :=
  Step.par.hcompCong modeIsUnivalent substitutedSidesStep substitutedCapStep

end hcompCong

/-! ### `glueIntroCong` (binary, mode-univalent gated, both at base).

Binary exemplar: two inner Step.par premises (base + partial),
both at the shared `baseType`.  `boundaryWitness : RawTerm scope`
is index data.  Mode hypothesis `mode = .univalent`. -/
namespace glueIntroCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
    {baseSource : Term sourceCtx baseType baseRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialSource : Term sourceCtx baseType partialRawSource}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (renamedBaseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (renamedPartialStep :
      Step.par (Term.rename termRenaming partialSource)
               (Term.rename termRenaming partialTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseSource partialSource))
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseTarget partialTarget)) :=
  Step.par.glueIntroCong modeIsUnivalent renamedBaseStep renamedPartialStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
    {baseSource : Term sourceCtx baseType baseRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialSource : Term sourceCtx baseType partialRawSource}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (substitutedBaseStep :
      Step.par (Term.subst termSubst baseSource)
               (Term.subst termSubst baseTarget))
    (substitutedPartialStep :
      Step.par (Term.subst termSubst partialSource)
               (Term.subst termSubst partialTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseSource partialSource))
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseTarget partialTarget)) :=
  Step.par.glueIntroCong modeIsUnivalent substitutedBaseStep substitutedPartialStep

end glueIntroCong

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

/-! ### `transpCong` (binary, mode-univalent, multi-arg cubical transport).

Binary exemplar with two inner Step.par premises: typePath at the
universe-typed Path, sourceValue at sourceType.  Mode hypothesis
`mode = .univalent`.  All other args (universeLevel, levelLt,
source/target types, source/target type raws) are explicit data,
not step subjects. -/
namespace transpCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
      RawTerm sourceScope}
    {typePathSource :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {typePathTarget :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (renamedTypePathStep :
      Step.par (Term.rename termRenaming typePathSource)
               (Term.rename termRenaming typePathTarget))
    (renamedSourceValueStep :
      Step.par (Term.rename termRenaming sourceValueSource)
               (Term.rename termRenaming sourceValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource))
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)) :=
  Step.par.transpCong modeIsUnivalent
    universeLevel universeLevelLt
    (sourceType.rename rho) (targetType.rename rho)
    (sourceTypeRaw.rename rho) (targetTypeRaw.rename rho)
    renamedTypePathStep renamedSourceValueStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
      RawTerm sourceScope}
    {typePathSource :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {typePathTarget :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (substitutedTypePathStep :
      Step.par (Term.subst termSubst typePathSource)
               (Term.subst termSubst typePathTarget))
    (substitutedSourceValueStep :
      Step.par (Term.subst termSubst sourceValueSource)
               (Term.subst termSubst sourceValueTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource))
      (Term.subst termSubst
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)) :=
  Step.par.transpCong modeIsUnivalent
    universeLevel universeLevelLt
    (sourceType.subst sigma) (targetType.subst sigma)
    (sourceTypeRaw.subst sigma.forRaw) (targetTypeRaw.subst sigma.forRaw)
    substitutedTypePathStep substitutedSourceValueStep

end transpCong

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
