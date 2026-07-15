import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.NatCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Normalize.RawTermNF
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidateArrow

/-! # FX1Poly/Core/NatElimNumeralStrongNormalization
    — the `natElim` / `natRec` cell-SN engine for a NORMAL scrutinee: reduces cell SN to the single firing
      contractum (an FTGEN-13.1 building block, NOT the closure — see the honest caveat on the numeral wrapper)

`StrongNormalizationNatElim.natElim_isStronglyNormalizing_of_strongly_normalizing_branches` proves the `natElim`
cell strongly normalizing from SN branches, but it threads the OVER-GENERAL residue

```
succContractumTerminates :
  ∀ currentMotive currentSucc predecessor currentZero, IsStronglyNormalizing predecessor →
    IsStronglyNormalizing (succ-ι contractum)
```

— a hypothesis quantified over EVERY strongly-normalizing predecessor.  That residue is unsatisfiable at the open
level: the contractum embeds the recursive `natElimCellSpine currentMotive predecessor …` at an arbitrary SN
predecessor, and raw recursors are not globally SN.  It is the single obstruction standing between the per-row
bounded fundamental theorem and the consistency leg's bare `elimFundamental` premise (the recursor-SN keystone).

This file ships the wrappers that REDUCE that residue to a single firing obligation — but do NOT discharge it
(the discharge needs Tait membership; see the honest caveat on the numeral wrapper).  For a scrutinee
that is a NORMAL FORM, the cell can only step by congruence into a branch or by an ι-firing — there is NO
scrutinee-congruence (the scrutinee is already normal).  So the cell SN needs the contractum SN ONLY at the single
predecessor the ι actually fires on, i.e. only when `scrutinee = natSuccCell predecessor`.  The premise

```
succContractumSN :
  ∀ currentMotive currentZero currentSucc predecessor, … → scrutinee = natSuccCell predecessor →
    IsStronglyNormalizing (succ-ι contractum)
```

is conditioned on the firing actually happening for THIS scrutinee — a single obligation, not a universal over all
predecessors.  When the scrutinee is a numeral `natSuccCell pred`, the structural numeral induction REDUCES that
firing obligation to a branch substitution-closure premise (`succBranchSubstClosed`): the recursive call
`natElimCellSpine currentMotive pred …` is SN by the inductive hypothesis (pred is structurally smaller), and the
substitution-closure must land the contractum.  HONEST CAVEAT: that `succBranchSubstClosed` premise is NOT itself
discharged here — it RELOCATES the false residue rather than eliminating it (it is universally false at open scope:
see the numeral wrapper's counterexample), so this file does NOT close FTGEN-13.1.  The genuine residue-free
discharge threads Tait MEMBERSHIP (CR2 + a uniform member-branch closure), which is the open #1754 work.

## Where the argument lives

The three-fold `Acc` tower is GENERATOR-AGNOSTIC and lives once, in
`NatShapedRecursorCellStrongNormalization.lean` — `gen_natElim` and `gen_natRec` share the v2 substrate's arity-4
metadata, so `Step.from_natElim` and `Step.from_natRec` are the same six-way inversion modulo the generator
constant.  `natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee` below adds the numeral induction over
that shared engine, once; the four `natElim` / `natRec` theorems instantiate it at their own spine and inversion.
The STATEMENTS are unchanged — only the duplicated towers and inductions are gone.

## Zero-axiom verification

The shared engine's `Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_natElim` /
`Step.from_natRec` inversions, and `RawTerm.isStepNormalForm_blocks_step`.  No induction-recursion, no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The recursor cell-SN engine for a NORMAL scrutinee (firing-reduced, not residue-free).**  A `natElim` cell
with a NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the contractum is strongly
normalizing whenever the scrutinee is a successor (`succContractumSN`).  This is a sound conditional that REDUCES the
cell-SN obligation to the single firing contractum; it does NOT discharge that contractum (see the numeral wrapper's
honest caveat — the discharge needs Tait membership, not bare SN).  Unlike
`natElim_isStronglyNormalizing_of_strongly_normalizing_branches`, the firing obligation is conditioned on the
scrutinee actually being `natSuccCell predecessor` — a single firing, not the over-general
`∀ predecessor, IsStronglyNormalizing predecessor → …` residue that is unsatisfiable for open terms.  The shared
nat-shaped three-fold `Acc.ndrec` engine on `(motive, zeroBranch, succBranch)` at the `natElim` spine and
inversion: scrutinee-congruence is impossible (the scrutinee is normal), ι-zero lands on the current zero branch,
ι-succ on the contractum (`succContractumSN`), and the three branch congruences recurse.  The keystone core that
the numeral-induction wrapper closes (the recursive call's SN comes from the structural numeral IH, discharging
`succContractumSN`). -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc →
        scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee
    (fun step => Step.from_natElim step)
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates succContractumSN

/-- **`natSucc` is injective.**  Two `natSuccCell` cells over equal predecessors are equal terms iff their
predecessors are equal — the constructor injectivity for `gen_natSucc`'s single child.  Mirrors
`pathLamValueCell_inj`: the `mkGen` injection exposes the children equality, then `RawTermChildren.childCons.inj`
projects the head (the indices coincide, so the injection emits a plain `Eq` head component).  Used by the
numeral wrapper to identify the `Step.from_natElim` successor witness with the structural predecessor. -/
theorem natSuccCell_inj {scope : Nat} {first second : RawTerm scope}
    (equal : natSuccCell first = natSuccCell second) : first = second := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **The nat-shaped recursor cell-SN for a NUMERAL scrutinee, modulo the substitution-closure residue.**  The
generator-agnostic numeral induction over the shared normal-scrutinee engine: a numeral is a normal form
(`isNatValue_impliesStepNormalForm`), so the engine reduces cell SN to the contractum SN at the firing
predecessor; at `natSuccCell pred` the recursive call `cellSpine currentMotive pred …` is strongly normalizing by
the structural inductive hypothesis (`pred` smaller, the IH universal over the branches), and
`succBranchSubstClosed` is asked to land the substituted contractum.  The successor witness from the inversion is
identified with the structural `pred` by `natSuccCell_inj`; the zero case's firing obligation is vacuous
(`natZeroCell ≠ natSuccCell _`).

Carries the HONEST CAVEAT of its instantiations: `succBranchSubstClosed` is UNIVERSALLY FALSE at open scope, so
this RELOCATES the residue rather than eliminating it.  See
`natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee` for the counterexample. -/
theorem natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee {scope : Nat}
    {cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope}
    (spineInversion : NatShapedSpineInversion cellSpine)
    {scrutinee : RawTerm scope}
    (scrutineeIsNatValue : IsNatValue scrutinee)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → IsNatValue predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc)) :
    ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
      IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (cellSpine motive scrutinee zeroBranch succBranch) := by
  induction scrutineeIsNatValue with
  | zero =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      exact natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee spineInversion
        (isNatValue_impliesStepNormalForm IsNatValue.zero)
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun _currentMotive _currentZero _currentSucc _predecessor _ _ _ scrutineeIsSucc =>
          Generator.noConfusion
            (congrArg RawTerm.rootGenerator scrutineeIsSucc :
              Generator.gen_natZero = Generator.gen_natSucc))
  | @succ pred predIsNatValue predIH =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      refine natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee spineInversion
        (isNatValue_impliesStepNormalForm (IsNatValue.succ predIsNatValue))
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun currentMotive currentZero currentSucc predecessor currentMotiveSN currentZeroSN
            currentSuccSN scrutineeIsSucc => ?_)
      have predEq : pred = predecessor := natSuccCell_inj scrutineeIsSucc
      subst predEq
      exact succBranchSubstClosed currentMotive currentZero currentSucc pred
        (cellSpine currentMotive pred currentZero currentSucc)
        currentMotiveSN currentZeroSN currentSuccSN predIsNatValue
        (predIH currentMotiveSN currentZeroSN currentSuccSN)

/-- **The recursor cell-SN for a NUMERAL scrutinee, modulo the substitution-closure residue (NOT FTGEN-13.1).**
A `natElim` cell whose scrutinee is a numeral (`IsNatValue`) and whose branches are strongly normalizing is
strongly normalizing — GIVEN `succBranchSubstClosed`.  The shared nat-shaped numeral induction at the `natElim`
spine and inversion: a numeral is a normal form (`isNatValue_impliesStepNormalForm`), so the normal-scrutinee
engine reduces cell SN to the contractum SN at the firing predecessor; at `natSuccCell pred` the recursive call
`natElimCellSpine currentMotive pred …` is strongly normalizing by the structural inductive hypothesis (`pred`
smaller, the IH universal over the branches), and `succBranchSubstClosed` is asked to land the substituted
contractum.
**HONEST CAVEAT (corrects an earlier "residue-free / FTGEN-13.1 closed" overclaim):** this RELOCATES the residue
rather than eliminating it.  `succBranchSubstClosed` — SN of the succ-branch substituted with an ARBITRARY SN
recursive result and a value predecessor — is itself UNIVERSALLY FALSE at open scope, by the same
substitution-does-not-preserve-SN counterexample that refutes `succContractumTerminates`:
`currentSucc := app (var 0) (var 0)` (a normal form, hence SN), `recursiveResult := lam (app (var 0) (var 0))`
(a value, hence SN) give the substituted contractum `(lam x. x x) (lam x. x x) = Ω`, which is NOT SN.  A bare-SN
recursive result cannot land the contractum.  The genuine residue-free discharge (FTGEN-13.1 #1754) must thread
Tait MEMBERSHIP: CR2 (`CanonicalFormsPredicate.closedUnderStep`) to keep the engine's STEPPED branches members,
plus a uniform member-branch contractum closure (member recursive result ⟹ member contractum) — which requires the
SN engine to carry membership, not just SN, through its `Acc` recursion.  This lemma is a sound implication and a
load-bearing building block, but it does NOT by itself close the recursor-SN keystone. -/
theorem natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsNatValue : IsNatValue scrutinee)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → IsNatValue predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc)) :
    ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
      IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee
    (fun step => Step.from_natElim step) scrutineeIsNatValue succBranchSubstClosed

/-- **The recursor cell-SN engine for a NORMAL scrutinee — the `natRec` twin.**  The same shared nat-shaped
three-fold engine as `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee`, instantiated at the `natRec`
spine and the `Step.from_natRec` inversion: `gen_natElim` and `gen_natRec` share the v2 substrate's metadata
(same arity-4 motive shape, same six-way inversion, the same numeral value predicate), so the firing-reduced
normal-scrutinee cell SN transfers verbatim — the firing obligation `succContractumSN` is conditioned on
`scrutinee = natSuccCell predecessor`, the recursive call inside the ι-succ contractum is the `natRec` cell, and
scrutinee-congruence is impossible on the normal scrutinee. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc →
        scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee
    (fun step => Step.from_natRec step)
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates succContractumSN

/-- **The recursor cell-SN for a NUMERAL scrutinee, modulo the substitution-closure residue — the `natRec` twin.**
The shared nat-shaped numeral induction at the `natRec` spine and the `Step.from_natRec` inversion — a numeral is a
normal form, the engine reduces cell SN to the ι-succ contractum SN, the recursive `natRecCellSpine currentMotive
pred …` is SN by the structural inductive hypothesis (`pred` smaller, the IH universal over branches), and the
(generator-agnostic) `succBranchSubstClosed` is asked to land the substituted contractum.  Carries the SAME HONEST
CAVEAT as the `natElim` wrapper: `succBranchSubstClosed` is UNIVERSALLY FALSE at open scope
(`(lam x. x x) (lam x. x x) = Ω` counterexample), so this RELOCATES rather than eliminates the residue and does NOT
close FTGEN-13.1 — the genuine discharge threads Tait MEMBERSHIP (CR2 + a uniform member-branch closure; the open
#1754 work). -/
theorem natRecCellSpine_isStronglyNormalizing_of_natValueScrutinee {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsNatValue : IsNatValue scrutinee)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → IsNatValue predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc)) :
    ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
      IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee
    (fun step => Step.from_natRec step) scrutineeIsNatValue succBranchSubstClosed

end StepStar
end FX1Poly.Core
