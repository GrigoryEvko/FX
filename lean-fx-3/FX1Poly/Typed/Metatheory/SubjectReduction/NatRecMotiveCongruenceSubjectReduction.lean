import FX1Poly.Typed.Metatheory.SubjectReduction.NatElimMotiveCongruenceSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.NatRecCongruenceSubjectReduction

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/NatRecMotiveCongruenceSubjectReduction
    — the `natRec` MOTIVE-position congruence subject reduction (the natElim motive arm, mirrored for the recursor)

The recursor twin of `natElimMotiveCongruenceSubjectReduction`.  `natRec` shares `natElim`'s dependent branch
type (`natElimDependentSuccBranchType`), the same output `subst0 motive scrutinee`, the same four-obligation
inversion shape (`invertAtNatRecHeadAllPremises`), and the same motive drift — so the proof is identical up to
`natRecCell` / `.gen_natRec` / `natRecElimRule`.  Reuses every ingredient the natElim arm built: the branch-type
drift + formedness (`natElimDependentSuccBranchType_isConvStableUnderMotiveStep` /
`_formed_ofMotive`), native context conversion (`HasTypeUnion.convertHeadBinding`), the `subst0`-output drift,
and `HasTypeUnion.natZeroTyped`.

## Zero-axiom verification

The shipped natRec inversion + validity + `reclassifyToType` + the natElim-arm branch/formedness/context-conversion
lemmas (each zero-axiom).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `natRec` congruence subject reduction at the MOTIVE position.**  The recursor mirror of
`natElimMotiveCongruenceSubjectReduction`: when the motive steps, the zero branch reclassifies through the
`subst0` drift to `subst0 motiveReduct natZeroCell`, the step branch is context-converted to `… .cons
motiveReduct` then reclassified through the succ-branch drift, and the output drifts by the motive `subst0`
congruence. -/
theorem HasTypeUnion.natRecMotiveCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive motiveReduct : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (natRecCell motive zeroBranch stepBranch scrutinee) classifier)
    (motiveStep : Step motive motiveReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (natRecCell motiveReduct zeroBranch stepBranch scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped, motiveTyped,
      classifierConv⟩ := HasTypeUnion.invertAtNatRecHeadAllPremises typed rfl
  obtain ⟨motiveReductType, motiveReductTyped, motiveTypeConv⟩ :=
    childSubjectReduction motiveTyped motiveStep
  have motiveReductAtUniverse : HasTypeUnion profile (context.cons natTypeCell) motiveReduct
      (universeCodeCell resultLevel resultFlag) :=
    HasTypeUnion.reclassifyToType motiveReductTyped motiveTypeConv.sym
      (UnionClassifierIsType.ofUniverseCode (context.cons natTypeCell) resultLevel resultFlag)
  have motiveIsType : UnionClassifierIsType profile (context.cons natTypeCell) motive :=
    ⟨resultLevel, resultFlag, motiveTyped⟩
  have zeroReductAtType : HasTypeUnion profile context zeroBranch
      (RawTerm.subst0 motiveReduct natZeroCell) :=
    HasTypeUnion.reclassifyToType zeroBranchTyped
      (Conv.subst0 (Conv.fromStep motiveStep) (Conv.refl natZeroCell))
      (UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context natTypeCell
        motiveReduct natZeroCell resultLevel resultFlag motiveReductAtUniverse
        (HasTypeUnion.natZeroTyped context))
  have stepBranchConverted : HasTypeUnion profile ((context.cons natTypeCell).cons motiveReduct)
      stepBranch (natElimDependentSuccBranchType motive) :=
    stepBranchTyped.convertHeadBinding (Conv.fromStep motiveStep) motiveIsType
  have stepReductAtType : HasTypeUnion profile ((context.cons natTypeCell).cons motiveReduct)
      stepBranch (natElimDependentSuccBranchType motiveReduct) :=
    HasTypeUnion.reclassifyToType stepBranchConverted
      (natElimDependentSuccBranchType_isConvStableUnderMotiveStep motiveStep)
      ⟨resultLevel, resultFlag, natElimDependentSuccBranchType_formed_ofMotive context motiveReduct
        resultLevel resultFlag motiveReductAtUniverse⟩
  refine ⟨RawTerm.subst0 motiveReduct scrutinee, ?_,
    classifierConv.sym.trans (Conv.subst0 (Conv.fromStep motiveStep) (Conv.refl scrutinee))⟩
  refine HasTypeUnion.elim context .gen_natRec natRecElimRule
    (.childCons motiveReduct (.childCons zeroBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
    .childNil resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact zeroReductAtType
    | tail _ hmem => cases hmem with
      | head => exact stepReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveReductAtUniverse
        | tail _ hmem => cases hmem

end FX1Poly.Typed
