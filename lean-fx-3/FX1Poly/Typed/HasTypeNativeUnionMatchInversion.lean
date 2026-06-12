import FX1Poly.Typed.HasTypeNativeUnionInversion

/-! # FX1Poly/Typed/HasTypeNativeUnionMatchInversion — NATIVE-37 part d: per-head inversions for the
    two-branch-match eliminator heads (boolElim / optionMatch / eitherMatch) + their REVERSE ADEQUACY.

This file extends the inversion substrate established in `HasTypeNativeUnionInversion` (four heads:
pathLam / lam / natElim / natSucc) to the three two-branch-match data-eliminator heads.  All three are
survivors of the SAME union arm — `twoBranchMatchElim` — pinned to their respective rows by the shipped
`nativeTwoBranchMatchRuleOf_cases` row inverter.

## The per-head inversion (the established recipe, replicated)

Each inversion takes a FREE subject + a `subjectShape : subject = <head-cell>` hypothesis, then `cases`
the union derivation (safe at a free index — never at the concrete cell index).  Exactly ONE arm
survives — the `twoBranchMatchElim` arm pinned to the head's row — and surfaces the three RECURSIVE
union premises (scrutinee + both branches) plus the row-parametric branch classifiers.  Every other arm
dies by one of the three killer classes (table-none `rfl`, `subjectIs…` head-clash, row-pin head-clash).

Critically, the `twoBranchMatchElim` arm ITSELF must be pinned to the CORRECT row: a `boolElim`-headed
subject cannot have been typed by the optionMatch or eitherMatch row, so two of the three row disjuncts
die by head clash too — only the matching row survives.

## ★ Reverse adequacy (closes the boolElim / optionMatch / eitherMatch share of fold 29)

For each family, a theorem of the form: a union typing of a `<head>`-headed subject yields the surfaced
RECURSIVE union premises (the honest surplus — the union types MORE, e.g. an eliminator whose scrutinee
is a computed value), AND when those surfaced premises happen to land in the bespoke engines (scrutinee
in the data-intro engine, branches in the grown engine) the bespoke `HasTypeDesc<Family>` derivation is
RECONSTRUCTED.  The honest-surplus disjunct is precisely the gap between the union-recursive scrutinee /
branch premises and the bespoke engine-specific premises: the union admits a scrutinee typed by ANY
native family, whereas the bespoke engine demands `HasTypeDescDataIntro` / `HasTypeDescOptionIntro` /
`HasTypeDescEitherIntro` and grown branches.  The reverse adequacy is therefore stated in the
RELATIVIZED form: the union derivation yields the bespoke derivation GIVEN that the surfaced premises are
bespoke-shaped (the reconstruction hypotheses); without them the surfaced union premises are the surplus.

## Zero-axiom

Free-subject `cases` + the shipped row inverter `nativeTwoBranchMatchRuleOf_cases` + head-generator
no-confusion + `rcases subjectShape with ⟨⟩` child drilling.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeUnionReverseAdequacy.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the boolElim head -/

/-- **★ Inversion at the boolElim head.**  A union typing of a `boolElimCell`-headed subject is EXACTLY a
two-branch-match typing at the `gen_boolElim` row: the scrutinee is union-typed at `Bool`, and both
branches are union-typed at the result classifier.  (The motive is stored, not premised — premise parity
with `HasTypeDescBoolElim`.)  No grown disjunct: `boolElimCell` is untypable in the grown engine (it is a
recursive eliminator in no host root). -/
theorem HasTypeNativeUnion.invertAtBoolElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = boolElimCell motive scrutinee thenBranch elseBranch) :
    HasTypeNativeUnion profile context scrutinee boolTypeCell ∧
    HasTypeNativeUnion profile context thenBranch classifier ∧
    HasTypeNativeUnion profile context elseBranch classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped,
        HasTypeNativeUnion.conv levelExpr flag thenBranchTyped converts reclassifierTyped,
        HasTypeNativeUnion.conv levelExpr flag elseBranchTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.boolElimCellHasNoTyping (fun contra => contra)
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
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨scrutineeTyped, firstBranchTyped, secondBranchTyped⟩
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

/-! ## (1) Inversion at the optionMatch head -/

/-- **★ Inversion at the optionMatch head.**  A union typing of an `optionMatchCell`-headed subject is
EXACTLY a two-branch-match typing at the `gen_optionMatch` row: for some element type `A`, the scrutinee
is union-typed at `option(A)`, the None branch is union-typed at the result classifier, and the Some
branch is union-typed at the non-dependent handler `A → C`.  No grown disjunct (`optionMatchCell` is a
recursive eliminator, untypable in the grown engine). -/
theorem HasTypeNativeUnion.invertAtOptionMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = optionMatchCell motive noneBranch someBranch scrutinee) :
    ∃ (elementType pinnedClassifier : RawTerm scope),
      HasTypeNativeUnion profile context scrutinee (optionTypeCell elementType) ∧
      HasTypeNativeUnion profile context noneBranch pinnedClassifier ∧
      HasTypeNativeUnion profile context someBranch
        (piTyCodeCell elementType (RawTerm.weaken pinnedClassifier)) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, pinnedClassifier, scrutineeTyped, noneTyped, someTyped, convInner⟩ :=
        innerInversion subjectShape
      exact ⟨elementType, pinnedClassifier, scrutineeTyped, noneTyped, someTyped,
        convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.optionMatchCellHasNoTyping (fun contra => contra)
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
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨typeParamA, _, scrutineeTyped, firstBranchTyped, secondBranchTyped,
          Conv.refl _⟩
      · subst ruleEq
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

/-! ## (1) Inversion at the eitherMatch head -/

/-- **★ Inversion at the eitherMatch head.**  A union typing of an `eitherMatchCell`-headed subject is
EXACTLY a two-branch-match typing at the `gen_eitherMatch` row: for some left/right types `A`, `B`, the
scrutinee is union-typed at `either(A, B)`, the left branch is union-typed at the handler `A → C`, and
the right branch is union-typed at `B → C`.  No grown disjunct (`eitherMatchCell` is a recursive
eliminator, untypable in the grown engine). -/
theorem HasTypeNativeUnion.invertAtEitherMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = eitherMatchCell motive leftBranch rightBranch scrutinee) :
    ∃ (leftType rightType pinnedClassifier : RawTerm scope),
      HasTypeNativeUnion profile context scrutinee (eitherTypeCell leftType rightType) ∧
      HasTypeNativeUnion profile context leftBranch
        (piTyCodeCell leftType (RawTerm.weaken pinnedClassifier)) ∧
      HasTypeNativeUnion profile context rightBranch
        (piTyCodeCell rightType (RawTerm.weaken pinnedClassifier)) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, pinnedClassifier, scrutineeTyped, leftTyped, rightTyped,
        convInner⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, pinnedClassifier, scrutineeTyped, leftTyped, rightTyped,
        convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.eitherMatchCellHasNoTyping (fun contra => contra)
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
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨typeParamA, typeParamB, _, scrutineeTyped, firstBranchTyped, secondBranchTyped,
          Conv.refl _⟩
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

end FX1Poly.Typed
