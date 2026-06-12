import FX1Poly.Typed.HasTypeNativeUnionInversion

/-! # FX1Poly/Typed/HasTypeNativeUnionPathProjInversion — NATIVE-37 part d: per-head inversions for the
    path-induction head (idJ) and the projection heads (fst / snd).

Two more eliminator shapes from the inversion substrate of `HasTypeNativeUnionInversion`:

  * **idJ** — the survivor is the `pathInductionElim` arm pinned to the `gen_idJ` row (the only row in
    `nativePathInductionRuleOf`).  Surfaced premises: the witness union-typed at a reflexive identity
    code `Id(typeCode, endpoint, endpoint)`, the base case union-typed at the result classifier.
  * **fst / snd** — the survivor is the `projectionElim` arm pinned to the `gen_fst` / `gen_snd` row.
    Surfaced premise: the pair term union-typed at `product(firstType, secondType)`; the classifier is
    forced to the selected component (`firstType` for fst, `secondType` for snd).

Both follow the established free-subject `cases` recipe with the three killer classes; the `idJCell`,
`fstCell`, `sndCell` heads are all untypable in the grown engine (host-head-untyped lemmas shipped), so
none carries an ofGrown disjunct.

## Zero-axiom

Free-subject `cases` + the shipped row inverters (`nativePathInductionRuleOf_cases` /
`nativeProjectionRuleOf_cases`) + head no-confusion + `rcases subjectShape with ⟨⟩`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the idJ head -/

/-- **★ Inversion at the idJ head.**  A union typing of an `idJCell`-headed subject is EXACTLY a
path-induction typing at the `gen_idJ` row: for some type code `A` and shared endpoint `x`, the witness
is union-typed at the reflexive identity code `Id(A, x, x)`, and the base case is union-typed at the
result classifier.  (The two-binder motive is stored, not premised — premise parity with
`HasTypeDescIdElim`.)  No grown disjunct: `idJCell` is untypable in the grown engine. -/
theorem HasTypeNativeUnion.invertAtIdJHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode endpoint : RawTerm scope,
      HasTypeNativeUnion profile context witness (idTypeCell typeCode endpoint endpoint) ∧
      HasTypeNativeUnion profile context baseCase classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨typeCode, endpoint, witnessTyped, baseCaseTyped⟩ := innerInversion subjectShape
      exact ⟨typeCode, endpoint, witnessTyped,
        HasTypeNativeUnion.conv levelExpr flag baseCaseTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.idJCellHasNoTyping (fun contra => contra)
  | baseTypeFormation context generator payload children rule isBaseType =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isBaseType (by intro tableHit; cases tableHit)
  | dataIntroNullary context generator payload children rule isDataIntro =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isDataIntro (by intro tableHit; cases tableHit)
  | flatFormation context generator payload children levels flag rule isFlatFormation premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFlatFormation (by intro tableHit; cases tableHit)
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
      rcases subjectShape with ⟨⟩
      exact ⟨armTypeCode, armEndpoint, witnessTyped, baseCaseTyped⟩
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

/-! ## (1) Inversion at the fst head -/

/-- **★ Inversion at the fst head.**  A union typing of an `fstCell`-headed subject is EXACTLY a
projection typing at the `gen_fst` row: for some second-component type `B`, the pair term is union-typed
at `product(C, B)` where `C` is the classifier, and the projected type is the first component (the
classifier).  No grown disjunct: `fstCell` is untypable in the grown engine. -/
theorem HasTypeNativeUnion.invertAtFstHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = fstCell pairTerm) :
    ∃ secondType pinnedClassifier : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm
        (productTypeCell pinnedClassifier secondType) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨secondType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨secondType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.fstCellHasNoTyping (fun contra => contra)
  | baseTypeFormation context generator payload children rule isBaseType =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isBaseType (by intro tableHit; cases tableHit)
  | dataIntroNullary context generator payload children rule isDataIntro =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isDataIntro (by intro tableHit; cases tableHit)
  | flatFormation context generator payload children levels flag rule isFlatFormation premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFlatFormation (by intro tableHit; cases tableHit)
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
  | projectionElim ctx generator rule armPairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨secondType, _, pairTyped, Conv.refl _⟩
      · subst ruleEq
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

/-! ## (1) Inversion at the snd head -/

/-- **★ Inversion at the snd head.**  A union typing of an `sndCell`-headed subject is EXACTLY a
projection typing at the `gen_snd` row: for some first-component type `A`, the pair term is union-typed
at `product(A, C)` where `C` is the classifier, and the projected type is the second component (the
classifier).  No grown disjunct: `sndCell` is untypable in the grown engine. -/
theorem HasTypeNativeUnion.invertAtSndHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = sndCell pairTerm) :
    ∃ firstType pinnedClassifier : RawTerm scope,
      HasTypeNativeUnion profile context pairTerm
        (productTypeCell firstType pinnedClassifier) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨firstType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨firstType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.sndCellHasNoTyping (fun contra => contra)
  | baseTypeFormation context generator payload children rule isBaseType =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isBaseType (by intro tableHit; cases tableHit)
  | dataIntroNullary context generator payload children rule isDataIntro =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isDataIntro (by intro tableHit; cases tableHit)
  | flatFormation context generator payload children levels flag rule isFlatFormation premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFlatFormation (by intro tableHit; cases tableHit)
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
  | projectionElim ctx generator rule armPairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨firstType, _, pairTyped, Conv.refl _⟩
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
