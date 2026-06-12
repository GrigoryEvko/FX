import FX1Poly.Typed.HasTypeNativeUnionInversion

/-! # FX1Poly/Typed/HasTypeNativeUnionRecursiveInversion — NATIVE-37 part d: per-head inversions for the
    remaining recursive eliminator heads (natRec and listElim).

The `natElim` head shipped in `HasTypeNativeUnionInversion`; this file adds its `gen_natRec` twin (the
second row of `nativeRecursiveElimRuleOf`) and the `listElim` head (the `listElim` arm).

  * **natRec** — survivor is the `recursiveElim` arm pinned to the `gen_natRec` row.  Surfaced premises:
    the scrutinee union-typed at `Nat`, the base (zero) branch union-typed at the classifier.  Identical
    in shape to `invertAtNatElimHead`, only the surviving row differs.
  * **listElim** — survivor is the `listElim` arm pinned to the `gen_listElim` row.  Surfaced premises
    are ALREADY the bespoke shapes (scrutinee LIST-INTRO-typed, branches GROWN-typed) — the listElim arm
    was added to the union with `HasTypeDescListIntro` / `HasTypeDescPi` premises (premise parity with
    `HasTypeDescListElim.listElimIntro`).  So this inversion surfaces the EXACT bespoke premises, and the
    reverse adequacy for listElim is UNCONDITIONAL (no relativization needed — the surplus is empty at
    this head).

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
`HasTypeNativeUnion.invertAtNatElimHead`. -/
theorem HasTypeNativeUnion.invertAtNatRecHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    HasTypeNativeUnion profile context scrutinee natTypeCell ∧
    HasTypeNativeUnion profile context zeroBranch classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨scrutineeTyped, zeroBranchTyped⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped,
        HasTypeNativeUnion.conv levelExpr flag zeroBranchTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natRecCellHasNoTyping (fun contra => contra)
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
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
  | recursiveUnaryIntro ctx generator rule armChild isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      rcases nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType with
          ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule armMotive armScrut armNil armCons elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (1) Inversion at the listElim head -/

/-- **★ Inversion at the listElim head.**  A union typing of a `listElimCell`-headed subject is EXACTLY a
listElim typing at the `gen_listElim` row.  UNIQUELY among the eliminator heads, the surfaced premises
are ALREADY the bespoke shapes: the scrutinee is LIST-INTRO-typed at `List(elementType)`, the nil branch
is GROWN-typed at the classifier, the cons branch is GROWN-typed at the 3-arg curried step type.  (The
union `listElim` arm was added with `HasTypeDescListIntro` / `HasTypeDescPi` premises — premise parity
with the bespoke `HasTypeDescListElim.listElimIntro`.)  No grown disjunct: `listElimCell` is untypable in
the grown engine. -/
theorem HasTypeNativeUnion.invertAtListElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = listElimCell motive scrutinee nilBranch consBranch) :
    ∃ elementType pinnedClassifier : RawTerm scope,
      HasTypeDescListIntro profile context scrutinee (listTypeCell elementType) ∧
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
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
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
  | recursiveUnaryIntro ctx generator rule armChild isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      rcases nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType with
          ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule armMotive armScrut armNil armCons elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      rcases subjectShape with ⟨⟩
      exact ⟨elementType, _, scrutineeTyped, nilBranchTyped, consBranchTyped, Conv.refl _⟩

end FX1Poly.Typed
