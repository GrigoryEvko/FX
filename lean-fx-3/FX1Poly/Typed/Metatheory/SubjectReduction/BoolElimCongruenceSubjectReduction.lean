import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionMatchInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/BoolElimCongruenceSubjectReduction
    — the `boolElim` recursor congruence subject reductions (gate-2 arms, TYTAB-2-FT-SR #1740)

The first DEPENDENT-recursor congruence arms of the eliminator-congruence subject reduction (gate 2 of the
consistency leg #1697).  `boolElim` has four children — the motive (binding one `bool` variable, hence at
scope+1 / the extended context `context.cons boolTypeCell`), the scrutinee, and the two nullary branches —
with output `subst0 motive scrutinee`.

This file ships the THREE child positions whose stepped child lives at the BASE context (`scrutinee`,
`thenBranch`, `elseBranch`); the motive-step arm (child at the extended context, with both branch classifiers
`subst0 motive constructor` drifting) is the genuinely harder fourth, shipped separately.

The congruence IH (`childSubjectReduction`) is CONTEXT-POLYMORPHIC — quantified over an arbitrary inner
context/scope — strictly more general than the projection arms' fixed-context IH, and exactly the shape the
eventual general congruence induction's per-obligation `ihPremises` supply (the motive obligation lives at the
extended context, so the IH must reach it).  Uniform proof: invert via `invertAtBoolElimHeadAllPremises` (all
four obligations, incl. the extended-context motive) → re-type the stepped child by the IH → reclassify it back
through validity → rebuild via the native `elim` arm → land the output `Conv` (a scrutinee step drifts the
output via `dependentEliminatorOutputType_isConvStableUnderScrutineeStep`; a branch step leaves it unchanged).

## Zero-axiom verification

The shipped inversion / validity / `reclassifyToType` / native `elim` arm / scrutinee-output congruence
composed with `Conv.sym` / `Conv.trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `boolElim` congruence subject reduction at the SCRUTINEE position.**  When the scrutinee steps, the
reformed cell re-types at the drifted output `subst0 motive scrutineeReduct` (`Conv`-bridged to the original by
`dependentEliminatorOutputType_isConvStableUnderScrutineeStep`).  Motive and branches are unchanged; the stepped
scrutinee is re-typed by the IH and reclassified back to `boolTypeCell`. -/
theorem HasTypeUnion.boolElimScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee scrutineeReduct thenBranch elseBranch classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) classifier)
    (scrutineeStep : Step scrutinee scrutineeReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (boolElimCell motive scrutineeReduct thenBranch elseBranch) pinned ∧
      Conv classifier pinned := by
  obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, ⟨motiveLevel, motiveFlag, motiveTyped⟩,
      classifierConv⟩ := HasTypeUnion.invertAtBoolElimHeadAllPremises typed rfl
  obtain ⟨scrutineeReductType, scrutineeReductTyped, scrutineeTypeConv⟩ :=
    childSubjectReduction scrutineeTyped scrutineeStep
  have boolIsType : UnionClassifierIsType profile context boolTypeCell :=
    HasTypeUnion.classifierIsType scrutineeTyped wellFormed
  have scrutineeReductAtBool : HasTypeUnion profile context scrutineeReduct boolTypeCell :=
    HasTypeUnion.reclassifyToType scrutineeReductTyped scrutineeTypeConv.sym boolIsType
  refine ⟨RawTerm.subst0 motive scrutineeReduct, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive
      scrutineeStep)⟩
  refine HasTypeUnion.elim context .gen_boolElim boolElimRule
    (.childCons motive (.childCons scrutineeReduct (.childCons thenBranch (.childCons elseBranch .childNil))))
    .childNil motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeReductAtBool
  | tail _ hmem => cases hmem with
    | head => exact thenBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact elseBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `boolElim` congruence subject reduction at the THEN-branch position.**  When the then-branch steps,
the output `subst0 motive scrutinee` is unchanged (branches do not occur in the output), so the result `Conv`
is the inversion's conversion leg directly.  The stepped branch is re-typed by the IH and reclassified back to
`subst0 motive boolTrueCell`. -/
theorem HasTypeUnion.boolElimThenBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch thenReduct elseBranch classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) classifier)
    (thenStep : Step thenBranch thenReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (boolElimCell motive scrutinee thenReduct elseBranch) pinned ∧
      Conv classifier pinned := by
  obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, ⟨motiveLevel, motiveFlag, motiveTyped⟩,
      classifierConv⟩ := HasTypeUnion.invertAtBoolElimHeadAllPremises typed rfl
  obtain ⟨thenReductType, thenReductTyped, thenTypeConv⟩ :=
    childSubjectReduction thenBranchTyped thenStep
  have thenIsType : UnionClassifierIsType profile context (RawTerm.subst0 motive boolTrueCell) :=
    HasTypeUnion.classifierIsType thenBranchTyped wellFormed
  have thenReductAtType :
      HasTypeUnion profile context thenReduct (RawTerm.subst0 motive boolTrueCell) :=
    HasTypeUnion.reclassifyToType thenReductTyped thenTypeConv.sym thenIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_boolElim boolElimRule
    (.childCons motive (.childCons scrutinee (.childCons thenReduct (.childCons elseBranch .childNil))))
    .childNil motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact thenReductAtType
    | tail _ hmem => cases hmem with
      | head => exact elseBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `boolElim` congruence subject reduction at the ELSE-branch position.**  The then-branch twin: the
output `subst0 motive scrutinee` is unchanged, and the stepped else-branch is re-typed by the IH and
reclassified back to `subst0 motive boolFalseCell`. -/
theorem HasTypeUnion.boolElimElseBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch elseReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) classifier)
    (elseStep : Step elseBranch elseReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, ⟨motiveLevel, motiveFlag, motiveTyped⟩,
      classifierConv⟩ := HasTypeUnion.invertAtBoolElimHeadAllPremises typed rfl
  obtain ⟨elseReductType, elseReductTyped, elseTypeConv⟩ :=
    childSubjectReduction elseBranchTyped elseStep
  have elseIsType : UnionClassifierIsType profile context (RawTerm.subst0 motive boolFalseCell) :=
    HasTypeUnion.classifierIsType elseBranchTyped wellFormed
  have elseReductAtType :
      HasTypeUnion profile context elseReduct (RawTerm.subst0 motive boolFalseCell) :=
    HasTypeUnion.reclassifyToType elseReductTyped elseTypeConv.sym elseIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_boolElim boolElimRule
    (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseReduct .childNil))))
    .childNil motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact thenBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact elseReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `boolElim` congruence subject reduction at the MOTIVE position (the hard sub-case).**  The motive
binds one `bool` variable, so it lives at scope+1 / the extended context `context.cons boolTypeCell`; when it
steps, BOTH branch classifiers `subst0 motive boolTrue/False` drift (to `subst0 motiveReduct …`), and the output
`subst0 motive scrutinee` drifts.  The stepped motive is re-typed by the (context-polymorphic) IH at the extended
context and reclassified back to its universe code (target-is-type unconditionally via `universeFormation`); each
branch is reclassified across `subst0_isConvStableUnderBodyStep` to the new branch-type, whose formedness comes
from `dependentMotiveOutputFormed_ofMotiveAndArgument` (the re-typed motive applied to `boolTrue`/`boolFalse`,
themselves typed at `boolTypeCell` via the nullary intro rows); the output drift is `Conv`-bridged by
`dependentEliminatorOutputType_isConvStableUnderMotiveStep`. -/
theorem HasTypeUnion.boolElimMotiveCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive motiveReduct : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) classifier)
    (motiveStep : Step motive motiveReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (boolElimCell motiveReduct scrutinee thenBranch elseBranch) pinned ∧
      Conv classifier pinned := by
  obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, ⟨motiveLevel, motiveFlag, motiveTyped⟩,
      classifierConv⟩ := HasTypeUnion.invertAtBoolElimHeadAllPremises typed rfl
  obtain ⟨motiveReductType, motiveReductTyped, motiveTypeConv⟩ :=
    childSubjectReduction motiveTyped motiveStep
  have univIsType : UnionClassifierIsType profile (context.cons boolTypeCell)
      (universeCodeCell motiveLevel motiveFlag) :=
    ⟨motiveLevel.lsucc, motiveFlag,
      HasTypeUnion.universeFormation (context.cons boolTypeCell) motiveLevel motiveFlag⟩
  have motiveReductAtUniv : HasTypeUnion profile (context.cons boolTypeCell) motiveReduct
      (universeCodeCell motiveLevel motiveFlag) :=
    HasTypeUnion.reclassifyToType motiveReductTyped motiveTypeConv.sym univIsType
  have boolTrueTyped : HasTypeUnion profile context boolTrueCell boolTypeCell :=
    HasTypeUnion.intro context .gen_boolTrue boolTrueIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial (fun _ hmem => nomatch hmem)
  have boolFalseTyped : HasTypeUnion profile context boolFalseCell boolTypeCell :=
    HasTypeUnion.intro context .gen_boolFalse boolFalseIntroRule .childNil .childNil
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial (fun _ hmem => nomatch hmem)
  have thenIsType : UnionClassifierIsType profile context (RawTerm.subst0 motiveReduct boolTrueCell) :=
    UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context boolTypeCell
      motiveReduct boolTrueCell motiveLevel motiveFlag motiveReductAtUniv boolTrueTyped
  have elseIsType : UnionClassifierIsType profile context (RawTerm.subst0 motiveReduct boolFalseCell) :=
    UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context boolTypeCell
      motiveReduct boolFalseCell motiveLevel motiveFlag motiveReductAtUniv boolFalseTyped
  have thenAtReduct : HasTypeUnion profile context thenBranch (RawTerm.subst0 motiveReduct boolTrueCell) :=
    HasTypeUnion.reclassifyToType thenBranchTyped
      (subst0_isConvStableUnderBodyStep boolTrueCell motiveStep) thenIsType
  have elseAtReduct : HasTypeUnion profile context elseBranch (RawTerm.subst0 motiveReduct boolFalseCell) :=
    HasTypeUnion.reclassifyToType elseBranchTyped
      (subst0_isConvStableUnderBodyStep boolFalseCell motiveStep) elseIsType
  refine ⟨RawTerm.subst0 motiveReduct scrutinee, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee
      motiveStep)⟩
  refine HasTypeUnion.elim context .gen_boolElim boolElimRule
    (.childCons motiveReduct (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
    .childNil motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact thenAtReduct
    | tail _ hmem => cases hmem with
      | head => exact elseAtReduct
      | tail _ hmem => cases hmem with
        | head => exact motiveReductAtUniv
        | tail _ hmem => cases hmem

end FX1Poly.Typed
