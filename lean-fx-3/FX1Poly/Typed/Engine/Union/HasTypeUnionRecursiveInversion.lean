import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion

/-! # FX1Poly/Typed/HasTypeUnionRecursiveInversion — NATIVE-37 part d: per-head inversions for the
    remaining recursive eliminator heads (natRec and listElim).

The `natElim` head shipped in `HasTypeUnionInversion`; this file adds its `gen_natRec` twin (the
second row of `nativeRecursiveElimRuleOf`) and the `listElim` head (the `listElim` arm).

  * **natRec** — survivor is the `recursiveElim` arm pinned to the `gen_natRec` row.  Surfaced premises:
    the scrutinee union-typed at `Nat`, the base (zero) branch union-typed at the classifier.  Identical
    in shape to `invertAtNatElimHead`, only the surviving row differs.
  * **listElim** — survivor is the `listElim` arm pinned to the `gen_listElim` row.  Surfaced premises:
    the scrutinee UNION-typed at `List(elementType)` (the NATIVE-42 re-shape made the scrutinee premise
    union-recursive, retiring the last zoo judgment named inside the union), the nil/cons branches
    GROWN-typed at the result / 3-arg curried step type.  The reverse adequacy for listElim is therefore
    RELATIVIZED like every other head (the scrutinee reconstruction map is where computed-list
    scrutinees fall outside the bespoke engine).

## Zero-axiom

Free-subject `cases` + the shipped row inverters + head no-confusion + `rcases subjectShape with ⟨⟩`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the natRec head -/

/-- **★ Inversion at the natRec head.**  A union typing of a `natRecCell`-headed subject is EXACTLY a
recursive-eliminator typing at the `gen_natRec` row: the scrutinee is union-typed at `Nat` and the base
(zero) branch is union-typed at the classifier.  (The motive and step branch are stored, not premised.)
No grown disjunct: `natRecCell` is untypable in the grown engine.  The `gen_natRec` twin of
`HasTypeUnion.invertAtNatElimHead`. -/
theorem HasTypeUnion.invertAtNatRecHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨scrutineeTyped, zeroBranchTyped⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped,
        HasTypeUnion.conv levelExpr flag zeroBranchTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natRecCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | dataIntroNullary context generator payload children rule isDataIntro =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isDataIntro (by intro tableHit; cases tableHit)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveElim ctx generator rule armMotive armBase armStep armScrut resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨scrutineeTyped, baseBranchTyped⟩
  | twoBranchMatchElim ctx generator rule armMotive armFirst armSecond armScrut
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule armMotive armBase armWitness armTypeCode armEndpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveDataIntro ctx generator spec head recursiveChild elementType isRecursiveDataIntro _ _ =>
      rcases recursiveDataIntroSpecOf_cases
          (show recursiveDataIntroSpecOf generator = some spec from isRecursiveDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ <;>
        subst specEq <;>
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | grownDataIntro ctx generator spec child0 child1 typeParam0 typeParam1 formednessLevel
      formednessFlag isGrownDataIntro _ _ _ =>
      rcases grownDataIntroSpecOf_cases
          (show grownDataIntroSpecOf generator = some spec from isGrownDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩
          | ⟨_, specEq⟩ <;>
        subst specEq <;>
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule armMotive armScrut armNil armCons elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (1) Inversion at the listElim head -/

/-- **★ Inversion at the listElim head.**  A union typing of a `listElimCell`-headed subject is EXACTLY a
listElim typing at the `gen_listElim` row: the scrutinee is UNION-typed at `List(elementType)` (the
NATIVE-42 union-recursive premise), the nil branch is GROWN-typed at the classifier, the cons branch is
GROWN-typed at the 3-arg curried step type.  No grown disjunct: `listElimCell` is untypable in the grown
engine. -/
theorem HasTypeUnion.invertAtListElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = listElimCell motive scrutinee nilBranch consBranch) :
    ∃ elementType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context scrutinee (listTypeCell elementType) ∧
      HasTypeDescPi profile context nilBranch pinnedClassifier ∧
      HasTypeDescPi profile context consBranch
        (listStepFunctionType elementType pinnedClassifier) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, pinnedClassifier, scrutineeTyped, nilTyped, consTyped, convInner⟩ :=
        innerInversion subjectShape
      exact ⟨elementType, pinnedClassifier, scrutineeTyped, nilTyped, consTyped,
        convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.listElimCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | dataIntroNullary context generator payload children rule isDataIntro =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isDataIntro (by intro tableHit; cases tableHit)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveElim ctx generator rule armMotive armBase armStep armScrut resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | twoBranchMatchElim ctx generator rule armMotive armFirst armSecond armScrut
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule armMotive armBase armWitness armTypeCode armEndpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveDataIntro ctx generator spec head recursiveChild elementType isRecursiveDataIntro _ _ =>
      rcases recursiveDataIntroSpecOf_cases
          (show recursiveDataIntroSpecOf generator = some spec from isRecursiveDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ <;>
        subst specEq <;>
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | grownDataIntro ctx generator spec child0 child1 typeParam0 typeParam1 formednessLevel
      formednessFlag isGrownDataIntro _ _ _ =>
      rcases grownDataIntroSpecOf_cases
          (show grownDataIntroSpecOf generator = some spec from isGrownDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩
          | ⟨_, specEq⟩ <;>
        subst specEq <;>
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule armMotive armScrut armNil armCons elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      rcases subjectShape with ⟨⟩
      exact ⟨elementType, _, scrutineeTyped, nilBranchTyped, consBranchTyped, Conv.refl _⟩

end FX1Poly.Typed
