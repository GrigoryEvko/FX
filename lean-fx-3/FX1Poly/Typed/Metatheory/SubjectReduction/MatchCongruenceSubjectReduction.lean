import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionMatchInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/MatchCongruenceSubjectReduction
    — the `optionMatch` / `eitherMatch` base-context congruence subject reductions (gate-2 arms, #1740)

The base-context congruence arms of the two coproduct/option matchers (gate 2 of the consistency leg #1697).
Both share `boolElim`'s shape — arity 4, `binderShifts = [1, 0, 0, 0]`, the motive a one-binder child at
`scope + 1` and the three other children (two branches + scrutinee) at the ambient base `scope` — so their
base-context arms are the exact `boolElim` mirror.  Unlike `boolElim`'s plain inversion, the `optionMatch` /
`eitherMatch` inversions ALREADY surface the extended-context motive obligation (the `∃ level flag` witness),
so no `AllPremises` companion is needed here.

This file ships the THREE base-context positions for each matcher — the `scrutinee` step (output drifts via
`dependentEliminatorOutputType_isConvStableUnderScrutineeStep`) and the two BRANCH steps (output unchanged,
the branch never occurs in `subst0 motive scrutinee`).  The branches' classifiers are dependent Π types
(`optionMatchDependentSomeBranchType` / `eitherMatchDependentInl/InrBranchType`) read off the motive, but a
branch step leaves the motive — hence those types — fixed, so the branch arms reclassify against the
unchanged branch type recovered from validity.  The motive step (which DRIFTS every branch's Π classifier)
is the harder sub-case, shipped separately once the dependent-branch-type congruence substrate lands.

`optionMatch`'s second type param is ignored by its rule's obligations (only `typeParamA = elementType`
appears), so the rebuild supplies `elementType` as the immaterial dummy; `eitherMatch` uses both params and
the inversion surfaces both.

## Zero-axiom verification

The shipped inversions / validity `classifierIsType` / `reclassifyToType` / native `elim` arm /
scrutinee-output congruence.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `optionMatch` congruence subject reduction at the SCRUTINEE position.**  When the scrutinee steps,
the reformed cell re-types at the drifted output `subst0 motive scrutineeReduct`; the stepped scrutinee is
re-typed by the IH and reclassified back to `optionTypeCell elementType`. -/
theorem HasTypeUnion.optionMatchScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch : RawTerm scope}
    {scrutinee scrutineeReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier)
    (scrutineeStep : Step scrutinee scrutineeReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (optionMatchCell motive noneBranch someBranch scrutineeReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, noneTyped, someTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtOptionMatchHead typed rfl
  obtain ⟨scrutineeReductType, scrutineeReductTyped, scrutineeTypeConv⟩ :=
    childSubjectReduction scrutineeTyped scrutineeStep
  have optionIsType : UnionClassifierIsType profile context (optionTypeCell elementType) :=
    HasTypeUnion.classifierIsType scrutineeTyped wellFormed
  have scrutineeReductAtOption :
      HasTypeUnion profile context scrutineeReduct (optionTypeCell elementType) :=
    HasTypeUnion.reclassifyToType scrutineeReductTyped scrutineeTypeConv.sym optionIsType
  refine ⟨RawTerm.subst0 motive scrutineeReduct, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive
      scrutineeStep)⟩
  refine HasTypeUnion.elim context .gen_optionMatch optionMatchElimRule
    (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutineeReduct .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeReductAtOption
  | tail _ hmem => cases hmem with
    | head => exact noneTyped
    | tail _ hmem => cases hmem with
      | head => exact someTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `optionMatch` congruence subject reduction at the NONE-branch position.**  The None branch does not
occur in the output `subst0 motive scrutinee`, so the output `Conv` is the inversion's conversion leg
directly; the stepped branch is re-typed by the IH and reclassified back to `subst0 motive optionNoneCell`. -/
theorem HasTypeUnion.optionMatchNoneBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch noneReduct someBranch scrutinee classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier)
    (noneStep : Step noneBranch noneReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (optionMatchCell motive noneReduct someBranch scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, noneTyped, someTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtOptionMatchHead typed rfl
  obtain ⟨noneReductType, noneReductTyped, noneTypeConv⟩ :=
    childSubjectReduction noneTyped noneStep
  have noneIsType : UnionClassifierIsType profile context (RawTerm.subst0 motive optionNoneCell) :=
    HasTypeUnion.classifierIsType noneTyped wellFormed
  have noneReductAtType :
      HasTypeUnion profile context noneReduct (RawTerm.subst0 motive optionNoneCell) :=
    HasTypeUnion.reclassifyToType noneReductTyped noneTypeConv.sym noneIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_optionMatch optionMatchElimRule
    (.childCons motive (.childCons noneReduct (.childCons someBranch (.childCons scrutinee .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact noneReductAtType
    | tail _ hmem => cases hmem with
      | head => exact someTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `optionMatch` congruence subject reduction at the SOME-branch position.**  The Some branch (typed
at the dependent Π `optionMatchDependentSomeBranchType motive elementType`) does not occur in the output, so
the output `Conv` is the inversion's leg; the stepped branch is reclassified back to its unchanged Π type. -/
theorem HasTypeUnion.optionMatchSomeBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch someReduct scrutinee classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch scrutinee) classifier)
    (someStep : Step someBranch someReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (optionMatchCell motive noneBranch someReduct scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, noneTyped, someTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtOptionMatchHead typed rfl
  obtain ⟨someReductType, someReductTyped, someTypeConv⟩ :=
    childSubjectReduction someTyped someStep
  have someIsType :
      UnionClassifierIsType profile context (optionMatchDependentSomeBranchType motive elementType) :=
    HasTypeUnion.classifierIsType someTyped wellFormed
  have someReductAtType :
      HasTypeUnion profile context someReduct
        (optionMatchDependentSomeBranchType motive elementType) :=
    HasTypeUnion.reclassifyToType someReductTyped someTypeConv.sym someIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_optionMatch optionMatchElimRule
    (.childCons motive (.childCons noneBranch (.childCons someReduct (.childCons scrutinee .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact noneTyped
    | tail _ hmem => cases hmem with
      | head => exact someReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `eitherMatch` congruence subject reduction at the SCRUTINEE position.**  When the scrutinee steps,
the reformed cell re-types at the drifted output `subst0 motive scrutineeReduct`; the stepped scrutinee is
re-typed by the IH and reclassified back to `eitherTypeCell leftType rightType`. -/
theorem HasTypeUnion.eitherMatchScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch : RawTerm scope}
    {scrutinee scrutineeReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier)
    (scrutineeStep : Step scrutinee scrutineeReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (eitherMatchCell motive leftBranch rightBranch scrutineeReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨leftType, rightType, scrutineeTyped, leftTyped, rightTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtEitherMatchHead typed rfl
  obtain ⟨scrutineeReductType, scrutineeReductTyped, scrutineeTypeConv⟩ :=
    childSubjectReduction scrutineeTyped scrutineeStep
  have eitherIsType : UnionClassifierIsType profile context (eitherTypeCell leftType rightType) :=
    HasTypeUnion.classifierIsType scrutineeTyped wellFormed
  have scrutineeReductAtEither :
      HasTypeUnion profile context scrutineeReduct (eitherTypeCell leftType rightType) :=
    HasTypeUnion.reclassifyToType scrutineeReductTyped scrutineeTypeConv.sym eitherIsType
  refine ⟨RawTerm.subst0 motive scrutineeReduct, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive
      scrutineeStep)⟩
  refine HasTypeUnion.elim context .gen_eitherMatch eitherMatchElimRule
    (.childCons motive
      (.childCons leftBranch (.childCons rightBranch (.childCons scrutineeReduct .childNil))))
    (.childCons leftType (.childCons rightType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeReductAtEither
  | tail _ hmem => cases hmem with
    | head => exact leftTyped
    | tail _ hmem => cases hmem with
      | head => exact rightTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `eitherMatch` congruence subject reduction at the LEFT-branch position.**  The left branch (typed
at the dependent Π `eitherMatchDependentInlBranchType motive leftType`) does not occur in the output, so the
output `Conv` is the inversion's leg; the stepped branch is reclassified back to its unchanged Π type. -/
theorem HasTypeUnion.eitherMatchLeftBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch leftReduct rightBranch scrutinee classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier)
    (leftStep : Step leftBranch leftReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (eitherMatchCell motive leftReduct rightBranch scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨leftType, rightType, scrutineeTyped, leftTyped, rightTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtEitherMatchHead typed rfl
  obtain ⟨leftReductType, leftReductTyped, leftTypeConv⟩ :=
    childSubjectReduction leftTyped leftStep
  have leftIsType :
      UnionClassifierIsType profile context (eitherMatchDependentInlBranchType motive leftType) :=
    HasTypeUnion.classifierIsType leftTyped wellFormed
  have leftReductAtType :
      HasTypeUnion profile context leftReduct
        (eitherMatchDependentInlBranchType motive leftType) :=
    HasTypeUnion.reclassifyToType leftReductTyped leftTypeConv.sym leftIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_eitherMatch eitherMatchElimRule
    (.childCons motive
      (.childCons leftReduct (.childCons rightBranch (.childCons scrutinee .childNil))))
    (.childCons leftType (.childCons rightType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact leftReductAtType
    | tail _ hmem => cases hmem with
      | head => exact rightTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `eitherMatch` congruence subject reduction at the RIGHT-branch position.**  The right branch (typed
at the dependent Π `eitherMatchDependentInrBranchType motive rightType`) does not occur in the output, so the
output `Conv` is the inversion's leg; the stepped branch is reclassified back to its unchanged Π type. -/
theorem HasTypeUnion.eitherMatchRightBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch rightReduct scrutinee classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) classifier)
    (rightStep : Step rightBranch rightReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (eitherMatchCell motive leftBranch rightReduct scrutinee) pinned ∧
      Conv classifier pinned := by
  obtain ⟨leftType, rightType, scrutineeTyped, leftTyped, rightTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtEitherMatchHead typed rfl
  obtain ⟨rightReductType, rightReductTyped, rightTypeConv⟩ :=
    childSubjectReduction rightTyped rightStep
  have rightIsType :
      UnionClassifierIsType profile context (eitherMatchDependentInrBranchType motive rightType) :=
    HasTypeUnion.classifierIsType rightTyped wellFormed
  have rightReductAtType :
      HasTypeUnion profile context rightReduct
        (eitherMatchDependentInrBranchType motive rightType) :=
    HasTypeUnion.reclassifyToType rightReductTyped rightTypeConv.sym rightIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_eitherMatch eitherMatchElimRule
    (.childCons motive
      (.childCons leftBranch (.childCons rightReduct (.childCons scrutinee .childNil))))
    (.childCons leftType (.childCons rightType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact leftTyped
    | tail _ hmem => cases hmem with
      | head => exact rightReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

end FX1Poly.Typed
