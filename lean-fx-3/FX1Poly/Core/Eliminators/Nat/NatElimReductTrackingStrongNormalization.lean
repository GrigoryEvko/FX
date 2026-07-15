import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization
import FX1Poly.Core.Eliminators.Nat.NatElimSuccContractumReductionCongruence
import FX1Poly.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/NatElimReductTrackingStrongNormalization
    — the REDUCT-TRACKING `natElim` / `natRec` cell-SN engines: the satisfiable-premise replacement for the
      false `succContractumSN` / `succBranchSubstClosed` firing obligation (the FTGEN-13.1 keystone engine)

`natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` (in `NatElimNumeralStrongNormalization.lean`)
reduces the cell-SN obligation to a firing obligation `succContractumSN` quantified over ARBITRARY strongly
normalizing branches `(currentMotive, currentZero, currentSucc)`.  That obligation is UNIVERSALLY FALSE at open
scope (the Omega counterexample: substitution does not preserve SN), because the engine exposes only the SN of
the stepped branches, not their PROVENANCE.

This file fixes that.  It threads, through the nested `Acc` recursions, a `StepStar` reachability witness from
each ORIGINAL branch to its current (stepped) value.  The firing obligation therefore receives `StepStar motive
currentMotive`, `StepStar zeroBranch currentZero`, `StepStar succBranch currentSucc` — exactly the witnesses
that make it SATISFIABLE: the substituted contractum at the stepped branches is a REDUCT of the contractum at
the originals (by `StepStar.natElimSuccContractumReduces`), so its SN follows from the original contractum's SN
(`IsStronglyNormalizing.descendStepStar`), and that original contractum SN is the genuine Tait MEMBERSHIP
obligation the value-reducibility arm already carries (CR1).

## Where the argument lives

The `Acc` towers themselves are GENERATOR-AGNOSTIC and live once, in
`NatShapedRecursorCellStrongNormalization.lean`: `gen_natElim` and `gen_natRec` share the v2 substrate's arity-4
metadata, so `Step.from_natElim` and `Step.from_natRec` are the same six-way inversion modulo the generator
constant (declared as such at `Step.from_natRec`'s definition site), and `natElimCellSpine` / `natRecCellSpine`
differ only in that constant.  Each theorem below therefore instantiates the shared engine at its own spine,
inversion, and contractum congruence.  The STATEMENTS are unchanged — only the duplicated `Acc` towers are gone.

## Zero-axiom verification

The shared engines' `Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_natElim` /
`Step.from_natRec` inversions, `RawTerm.isStepNormalForm_blocks_step`, `IsStronglyNormalizing.descendStepStar`,
`StepStar.natElimSuccContractumReduces` / `StepStar.natRecSuccContractumReduces`, and `StepStar.single` /
`StepStar.trans_compose`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration swept by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The reduct-tracking `natElim` cell-SN engine (satisfiable firing premise).**  A `natElim` cell with a
NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the REACHABILITY-AWARE firing
obligation `firingContractumSN`: whenever the scrutinee is a successor `natSuccCell predecessor` and the current
branches are reachable from the originals, the substituted succ-iota contractum at the current branches is
strongly normalizing.  Unlike `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee`, whose firing
obligation quantifies over arbitrary SN currents and is therefore unsatisfiable at open scope, this obligation
receives `StepStar` witnesses (`motive` reaches `currentMotive` etc.), making it dischargeable from the original
contractum's SN via `StepStar.natElimSuccContractumReduces` + `descendStepStar`.  The shared nat-shaped engine
(three nested `Acc.ndrec` on the branch accessibilities, each motive carrying its reachability witness) at the
`natElim` spine and inversion. -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (firingContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc → scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    (fun step => Step.from_natElim step)
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates firingContractumSN

/-- **The reduct-tracking `natRec` cell-SN engine (satisfiable firing premise) — the `natRec` twin.**  The same
shared nat-shaped engine as `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability`,
instantiated at the `natRec` spine and the `Step.from_natRec` inversion (the two recursors share the v2
substrate's arity-4 metadata and six-way inversion).  The reachability thread through the three nested
`Acc.ndrec` makes the firing obligation `firingContractumSN` satisfiable from the original contractum's SN via
`StepStar.natRecSuccContractumReduces` + `IsStronglyNormalizing.descendStepStar`. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (firingContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc → scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    (fun step => Step.from_natRec step)
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates firingContractumSN

/-- **The `natElim` cell-SN theorem with a SATISFIABLE original-contractum-SN premise (the member-discharged
connector).**  Composes the reachability engine with the succ-iota contractum reduction-congruence: the engine's
`firingContractumSN` obligation at the stepped branches is discharged by `IsStronglyNormalizing.descendStepStar`
from the SN of the substituted succ-iota contractum at the ORIGINAL branches — `StepStar.natElimSuccContractumReduces`
carries the former to the latter as a reduct.  The remaining `originalContractumSN` premise (SN of the contractum
at the original branches, keyed on the firing equation `scrutinee = natSuccCell predecessor`) is exactly the CR1
shadow of the Tait member the value-reducibility arm already carries; unlike the engine's raw firing obligation it
quantifies over NO arbitrary currents, so it is the usable interface for the consumer rewire. -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates
    (fun _currentMotive _currentZero _currentSucc predecessor motiveChain zeroChain succChain scrutineeIsSucc =>
      IsStronglyNormalizing.descendStepStar
        (originalContractumSN predecessor scrutineeIsSucc)
        (natElimSuccContractumReduces motiveChain zeroChain succChain))

/-- **The `natRec` twin of the member-discharged connector.**  Same composition as the `natElim` connector with
`natRecCellSpine` and `StepStar.natRecSuccContractumReduces`. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates
    (fun _currentMotive _currentZero _currentSucc predecessor motiveChain zeroChain succChain scrutineeIsSucc =>
      IsStronglyNormalizing.descendStepStar
        (originalContractumSN predecessor scrutineeIsSucc)
        (natRecSuccContractumReduces motiveChain zeroChain succChain))

/-- **The reduct-tracking `natElim` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise).**  The
four-fold reachability generalization of `…_of_normalScrutinee_fromOriginalContractumSN`: the scrutinee need not
be normal — it is merely strongly normalizing — and the engine recurses on the scrutinee as well as the three
branches, threading a `StepStar` reachability witness through ALL FOUR `Acc.ndrec` levels.  The firing obligation
is replaced by the satisfiable `originalContractumSN`, keyed on the scrutinee REACHING a successor cell
(`StepStar scrutinee (natSuccCell predecessor)`): at the firing the scrutinee reachability identifies the
predecessor, the original contractum SN comes from `originalContractumSN`, and the stepped-branch contractum is
its reduct by `StepStar.natElimSuccContractumReduces` + `descendStepStar`.  This is the honest replacement for the
universally-false bare-SN firing premise of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches` — the
scrutinee-reducing root the recursor value-reducibility consumers actually call.  The shared nat-shaped four-fold
engine at the `natElim` spine, inversion, and contractum congruence. -/
theorem natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), StepStar scrutinee (natSuccCell predecessor) →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
    (fun step => Step.from_natElim step)
    (fun motiveChain zeroChain succChain => natElimSuccContractumReduces motiveChain zeroChain succChain)
    scrutineeTerminates motiveTerminates zeroBranchTerminates succBranchTerminates originalContractumSN

/-- **The reduct-tracking `natRec` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise)** — the
`natRec` twin of `natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`.  The same
shared nat-shaped four-fold engine at the `natRec` spine, the `Step.from_natRec` inversion, and
`StepStar.natRecSuccContractumReduces`; the recursors share the v2 substrate's arity-4 metadata, six-way
inversion, and the 2-substituent succ-iota contractum shape. -/
theorem natRecCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), StepStar scrutinee (natSuccCell predecessor) →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
    (fun step => Step.from_natRec step)
    (fun motiveChain zeroChain succChain => natRecSuccContractumReduces motiveChain zeroChain succChain)
    scrutineeTerminates motiveTerminates zeroBranchTerminates succBranchTerminates originalContractumSN

end StepStar
end FX1Poly.Core
