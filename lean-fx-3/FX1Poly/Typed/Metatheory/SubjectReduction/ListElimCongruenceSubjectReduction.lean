import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionRecursiveInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ListElimCongruenceSubjectReduction
    — the `listElim` base-context congruence subject reductions (gate-2 arms, TYTAB-2-FT-SR #1740)

The base-context congruence arms of the list recursor (gate 2 of the consistency leg #1697).  `listElim`
shares the `optionMatch` / `eitherMatch` shape — arity 4, `binderShifts = [1, 0, 0, 0]`, the motive a
one-binder child at `scope + 1` and the three other children (scrutinee + nil/cons branches) at the ambient
base `scope` (the cons branch's two-binder structure is carried by its dependent Π classifier
`listElimDependentConsBranchType motive elementType`, NOT by an extended typing context) — and its inversion
`invertAtListElimHead` already surfaces the extended-context motive obligation, so no `AllPremises` companion is
needed.

This file ships all THREE base-context child positions — the `scrutinee` step (output drifts via
`dependentEliminatorOutputType_isConvStableUnderScrutineeStep`) and the `nilBranch` / `consBranch` steps
(output unchanged — neither branch occurs in `subst0 motive scrutinee`).  A branch step leaves the motive — and
hence both branch classifiers — fixed, so the branch arms reclassify against the unchanged branch type from
validity.  The motive step (which DRIFTS the cons-branch Π classifier) is the harder sub-case, shipped
separately once the dependent-branch-type congruence substrate lands.

`listElim`'s second type param (the result type) is ignored by its rule's obligations (only
`elementType = typeParamA` appears), so the rebuild supplies `elementType` as the immaterial dummy.  The cell
argument order is `(motive, scrutinee, nilBranch, consBranch)`; the obligation order is
`[scrutinee, nilBranch, consBranch, motive]`.

## Zero-axiom verification

The shipped inversion / validity `classifierIsType` / `reclassifyToType` / native `elim` arm /
scrutinee-output congruence.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `listElim` congruence subject reduction at the SCRUTINEE position.**  When the scrutinee steps, the
reformed cell re-types at the drifted output `subst0 motive scrutineeReduct`; the stepped scrutinee is re-typed
by the IH and reclassified back to `listTypeCell elementType`. -/
theorem HasTypeUnion.listElimScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {nilBranch consBranch : RawTerm scope}
    {scrutinee scrutineeReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier)
    (scrutineeStep : Step scrutinee scrutineeReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (listElimCell motive scrutineeReduct nilBranch consBranch) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, nilTyped, consTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtListElimHead typed rfl
  obtain ⟨scrutineeReductType, scrutineeReductTyped, scrutineeTypeConv⟩ :=
    childSubjectReduction scrutineeTyped scrutineeStep
  have listIsType : UnionClassifierIsType profile context (listTypeCell elementType) :=
    HasTypeUnion.classifierIsType scrutineeTyped wellFormed
  have scrutineeReductAtList :
      HasTypeUnion profile context scrutineeReduct (listTypeCell elementType) :=
    HasTypeUnion.reclassifyToType scrutineeReductTyped scrutineeTypeConv.sym listIsType
  refine ⟨RawTerm.subst0 motive scrutineeReduct, ?_,
    classifierConv.sym.trans (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive
      scrutineeStep)⟩
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons scrutineeReduct (.childCons nilBranch (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeReductAtList
  | tail _ hmem => cases hmem with
    | head => exact nilTyped
    | tail _ hmem => cases hmem with
      | head => exact consTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `listElim` congruence subject reduction at the NIL-branch position.**  The nil branch does not occur
in the output `subst0 motive scrutinee`, so the output `Conv` is the inversion's conversion leg directly; the
stepped branch is re-typed by the IH and reclassified back to `subst0 motive listNilCell`. -/
theorem HasTypeUnion.listElimNilBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch nilReduct consBranch classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier)
    (nilStep : Step nilBranch nilReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (listElimCell motive scrutinee nilReduct consBranch) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, nilTyped, consTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtListElimHead typed rfl
  obtain ⟨nilReductType, nilReductTyped, nilTypeConv⟩ :=
    childSubjectReduction nilTyped nilStep
  have nilIsType : UnionClassifierIsType profile context (RawTerm.subst0 motive listNilCell) :=
    HasTypeUnion.classifierIsType nilTyped wellFormed
  have nilReductAtType :
      HasTypeUnion profile context nilReduct (RawTerm.subst0 motive listNilCell) :=
    HasTypeUnion.reclassifyToType nilReductTyped nilTypeConv.sym nilIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons scrutinee (.childCons nilReduct (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact nilReductAtType
    | tail _ hmem => cases hmem with
      | head => exact consTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `listElim` congruence subject reduction at the CONS-branch position.**  The cons branch (typed at
the dependent Π `listElimDependentConsBranchType motive elementType`) does not occur in the output, so the
output `Conv` is the inversion's leg; the stepped branch is reclassified back to its unchanged Π type. -/
theorem HasTypeUnion.listElimConsBranchCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch consReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context
      (listElimCell motive scrutinee nilBranch consBranch) classifier)
    (consStep : Step consBranch consReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context
        (listElimCell motive scrutinee nilBranch consReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨elementType, scrutineeTyped, nilTyped, consTyped, classifierConv,
      resultLevel, resultFlag, motiveTyped⟩ := HasTypeUnion.invertAtListElimHead typed rfl
  obtain ⟨consReductType, consReductTyped, consTypeConv⟩ :=
    childSubjectReduction consTyped consStep
  have consIsType :
      UnionClassifierIsType profile context (listElimDependentConsBranchType motive elementType) :=
    HasTypeUnion.classifierIsType consTyped wellFormed
  have consReductAtType :
      HasTypeUnion profile context consReduct
        (listElimDependentConsBranchType motive elementType) :=
    HasTypeUnion.reclassifyToType consReductTyped consTypeConv.sym consIsType
  refine ⟨RawTerm.subst0 motive scrutinee, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consReduct .childNil))))
    (.childCons elementType (.childCons elementType .childNil))
    resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact nilTyped
    | tail _ hmem => cases hmem with
      | head => exact consReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

end FX1Poly.Typed
