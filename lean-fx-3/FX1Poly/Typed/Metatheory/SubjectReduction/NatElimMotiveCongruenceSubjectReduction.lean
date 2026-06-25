import FX1Poly.Typed.Metatheory.SubjectReduction.NatElimCongruenceSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeMotiveCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeFormedFromMotive
import FX1Poly.Typed.Metatheory.ContextConversion.HasTypeUnionContextConversion

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/NatElimMotiveCongruenceSubjectReduction
    — the `natElim` / `natRec` MOTIVE-position congruence subject reduction (the hard arm — first complete motive arm)

The genuinely hard child position of the eliminator-congruence subject reduction: when the MOTIVE steps
`motive ⟶ motive'`, the eliminator's dependent branch classifiers ALL drift (`subst0 motive natZero ⟶ subst0
motive' natZero`, `natElimDependentSuccBranchType motive ⟶ … motive'`) AND the step branch's binder-extended
CONTEXT drifts (its `motive` binding becomes `motive'`).  Re-typing demands the three ingredients the
non-motive arms (`NatElimCongruenceSubjectReduction.lean`'s scrutinee / zero / step arms) did NOT need:

  * **branch-classifier drift** — `Conv.subst0` (zero branch) + `natElimDependentSuccBranchType_isConvStable-
    UnderMotiveStep` (step branch);
  * **drifted-classifier formedness** (type-SR) — `dependentMotiveOutputFormed_ofMotiveAndArgument` (zero
    branch's `subst0 motive' natZero`) + `natElimDependentSuccBranchType_formed_ofMotive` (the two-binder step
    branch's `natElimDependentSuccBranchType motive'`);
  * **context conversion** — `HasTypeUnion.convertHeadBinding` re-homes the step branch from `… .cons motive`
    to `… .cons motive'`.

This is the FIRST complete eliminator MOTIVE arm — the template the other data eliminators
(bool / option / either / list / idJ) mirror.  `natRec` is the identical proof (same branch type, same
formedness, same drift; only `natRecCell` / `natRecElimRule` differ).

## Zero-axiom verification

The shipped inversion (`invertAtNatElimHeadAllPremises`) + validity (`classifierIsType` /
`dependentMotiveOutputFormed` / `ofUniverseCode`) + `reclassifyToType` + the native `elim` arm + the drift /
formedness / context-conversion lemmas (each itself zero-axiom).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`natZeroCell` is union-typed at `natTypeCell`** — the nullary `natZero` intro row (no premises). -/
theorem HasTypeUnion.natZeroTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeUnion profile context natZeroCell natTypeCell := by
  refine HasTypeUnion.intro context .gen_natZero natZeroIntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
  intro obligation hmem; cases hmem

/-- **The `natElim` congruence subject reduction at the MOTIVE position.**  When the motive steps, the reformed
cell re-types at the drifted output `subst0 motiveReduct scrutinee`.  The zero branch is reclassified through the
`subst0` drift to `subst0 motiveReduct natZeroCell` (formed by `dependentMotiveOutputFormed`); the step branch is
first context-converted to `… .cons motiveReduct` then reclassified through the succ-branch drift to
`natElimDependentSuccBranchType motiveReduct` (formed by `natElimDependentSuccBranchType_formed_ofMotive`); the
motive itself is re-typed by the IH and reclassified back to its universe code. -/
theorem HasTypeUnion.natElimMotiveCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive motiveReduct : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (natElimCell motive zeroBranch stepBranch scrutinee) classifier)
    (motiveStep : Step motive motiveReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (natElimCell motiveReduct zeroBranch stepBranch scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped, motiveTyped,
      classifierConv⟩ := HasTypeUnion.invertAtNatElimHeadAllPremises typed rfl
  -- Re-type the stepped motive and reclassify it back to its universe code (universe rigidity).
  obtain ⟨motiveReductType, motiveReductTyped, motiveTypeConv⟩ :=
    childSubjectReduction motiveTyped motiveStep
  have motiveReductAtUniverse : HasTypeUnion profile (context.cons natTypeCell) motiveReduct
      (universeCodeCell resultLevel resultFlag) :=
    HasTypeUnion.reclassifyToType motiveReductTyped motiveTypeConv.sym
      (UnionClassifierIsType.ofUniverseCode (context.cons natTypeCell) resultLevel resultFlag)
  have motiveIsType : UnionClassifierIsType profile (context.cons natTypeCell) motive :=
    ⟨resultLevel, resultFlag, motiveTyped⟩
  -- Zero branch: reclassify through the `subst0` drift to the formed `subst0 motiveReduct natZeroCell`.
  have zeroReductAtType : HasTypeUnion profile context zeroBranch
      (RawTerm.subst0 motiveReduct natZeroCell) :=
    HasTypeUnion.reclassifyToType zeroBranchTyped
      (Conv.subst0 (Conv.fromStep motiveStep) (Conv.refl natZeroCell))
      (UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context natTypeCell
        motiveReduct natZeroCell resultLevel resultFlag motiveReductAtUniverse
        (HasTypeUnion.natZeroTyped context))
  -- Step branch: context-convert to `… .cons motiveReduct`, then reclassify through the succ-branch drift.
  have stepBranchConverted : HasTypeUnion profile ((context.cons natTypeCell).cons motiveReduct)
      stepBranch (natElimDependentSuccBranchType motive) :=
    stepBranchTyped.convertHeadBinding (Conv.fromStep motiveStep) motiveIsType
  have stepReductAtType : HasTypeUnion profile ((context.cons natTypeCell).cons motiveReduct)
      stepBranch (natElimDependentSuccBranchType motiveReduct) :=
    HasTypeUnion.reclassifyToType stepBranchConverted
      (natElimDependentSuccBranchType_isConvStableUnderMotiveStep motiveStep)
      ⟨resultLevel, resultFlag, natElimDependentSuccBranchType_formed_ofMotive context motiveReduct
        resultLevel resultFlag motiveReductAtUniverse⟩
  -- Rebuild the eliminator cell with the stepped motive; the output drifts by the motive `subst0` congruence.
  refine ⟨RawTerm.subst0 motiveReduct scrutinee, ?_,
    classifierConv.sym.trans (Conv.subst0 (Conv.fromStep motiveStep) (Conv.refl scrutinee))⟩
  refine HasTypeUnion.elim context .gen_natElim natElimRule
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
