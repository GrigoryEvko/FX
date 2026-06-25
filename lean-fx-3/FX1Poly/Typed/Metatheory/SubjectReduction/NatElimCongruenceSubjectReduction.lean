import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/NatElimCongruenceSubjectReduction
    — the `natElim` base-context congruence subject reductions (gate-2 arms, TYTAB-2-FT-SR #1740)

The base-context congruence arms of the `natElim` recursor (gate 2 of the consistency leg #1697).  `natElim`
has four children — the motive (one-`nat`-binder), the zero branch, the two-`nat`-binder step branch, and the
scrutinee — with obligation order `[scrutinee, baseBranch, stepBranch, motive]` (`natElimRule`) and output
`subst0 motive scrutinee`.

This file ships the two child positions whose stepped child lives at the BASE context — the `scrutinee` and the
`zeroBranch` (`baseBranch`).  The motive-step (one-binder extended context, via the proven boolElim recipe) and
the step-branch-step (two-binder extended context, needing the succ-branch-type congruence) are the harder pair,
shipped separately.

Uniform proof (the established recipe): invert via `invertAtNatElimHeadAllPremises` (all four obligations incl.
the extended-context step branch + motive) → re-type the stepped child by the context-polymorphic IH →
reclassify it back through validity → rebuild via the native `elim` arm → land the output `Conv` (a scrutinee
step drifts the output via `dependentEliminatorOutputType_isConvStableUnderScrutineeStep`; a base-branch step
leaves it unchanged).

## Zero-axiom verification

The shipped inversion / validity / `reclassifyToType` / native `elim` arm / scrutinee-output congruence.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `natElim` congruence subject reduction at the SCRUTINEE position.**  When the scrutinee steps, the
reformed cell re-types at the drifted output `subst0 motive scrutineeReduct`; motive and both branches are
unchanged.  The stepped scrutinee is re-typed by the IH and reclassified back to `natTypeCell`. -/
theorem HasTypeUnion.natElimScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    {scrutinee scrutineeReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (natElimCell motive zeroBranch stepBranch scrutinee) classifier)
    (scrutineeStep : Step scrutinee scrutineeReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (natElimCell motive zeroBranch stepBranch scrutineeReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped, motiveTyped,
      classifierConv⟩ := HasTypeUnion.invertAtNatElimHeadAllPremises typed rfl
  obtain ⟨scrutineeReductType, scrutineeReductTyped, scrutineeTypeConv⟩ :=
    childSubjectReduction scrutineeTyped scrutineeStep
  have natIsType : UnionClassifierIsType profile context natTypeCell :=
    HasTypeUnion.classifierIsType scrutineeTyped wellFormed
  have scrutineeReductAtNat : HasTypeUnion profile context scrutineeReduct natTypeCell :=
    HasTypeUnion.reclassifyToType scrutineeReductTyped scrutineeTypeConv.sym natIsType
  refine ⟨RawTerm.subst0 motive scrutineeReduct, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive
      scrutineeStep)⟩
  refine HasTypeUnion.elim context .gen_natElim natElimRule
    (.childCons motive (.childCons zeroBranch (.childCons stepBranch (.childCons scrutineeReduct .childNil))))
    .childNil resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeReductAtNat
  | tail _ hmem => cases hmem with
    | head => exact zeroBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact stepBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `natElim` congruence subject reduction at the ZERO-branch position.**  When the zero branch steps,
the output `subst0 motive scrutinee` is unchanged (the branch does not occur in the output), so the result
`Conv` is the inversion's conversion leg directly.  The stepped branch is re-typed by the IH and reclassified
back to `subst0 motive natZeroCell`. -/
theorem HasTypeUnion.natElimZeroBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch zeroReduct : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (natElimCell motive zeroBranch stepBranch scrutinee) classifier)
    (zeroStep : Step zeroBranch zeroReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (natElimCell motive zeroReduct stepBranch scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped, motiveTyped,
      classifierConv⟩ := HasTypeUnion.invertAtNatElimHeadAllPremises typed rfl
  obtain ⟨zeroReductType, zeroReductTyped, zeroTypeConv⟩ :=
    childSubjectReduction zeroBranchTyped zeroStep
  have zeroIsType : UnionClassifierIsType profile context (RawTerm.subst0 motive natZeroCell) :=
    HasTypeUnion.classifierIsType zeroBranchTyped wellFormed
  have zeroReductAtType :
      HasTypeUnion profile context zeroReduct (RawTerm.subst0 motive natZeroCell) :=
    HasTypeUnion.reclassifyToType zeroReductTyped zeroTypeConv.sym zeroIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_natElim natElimRule
    (.childCons motive (.childCons zeroReduct (.childCons stepBranch (.childCons scrutinee .childNil))))
    .childNil resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact zeroReductAtType
    | tail _ hmem => cases hmem with
      | head => exact stepBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

end FX1Poly.Typed
