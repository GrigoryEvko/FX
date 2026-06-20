import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion

/-! # FX1Poly/Typed/HasTypeUnionPathProjInversion — NATIVE-37 part d: per-head inversions for the
    path-induction head (idJ) and the projection heads (fst / snd).

Two more eliminator shapes from the inversion substrate of `HasTypeUnionInversion`:

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
theorem HasTypeUnion.invertAtIdJHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode endpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode endpoint endpoint) ∧
      HasTypeUnion profile context baseCase classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨typeCode, endpoint, witnessTyped, baseCaseTyped⟩ := innerInversion subjectShape
      exact ⟨typeCode, endpoint, witnessTyped,
        HasTypeUnion.conv levelExpr flag baseCaseTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.idJCellHasNoTyping (fun contra => contra)
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
  | elim ctx generator rule args params isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_idJ` row survives (its member cell IS the idJ cell);
      -- the other ten eliminator heads clash with the `idJ` subject head.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natRec
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ idJ — the SURVIVOR.  Destructure the children + params, recover the children from
      -- `subjectShape`, and surface the witness + base-case premises from `premisesHold`.
      · match args, params with
        | .childCons _armMotive (.childCons _armBase (.childCons _armWitness .childNil)),
          .childCons _armTypeCode (.childCons _armEndpoint (.childCons _resultType .childNil)) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
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

/-! ## (1) Inversion at the fst head -/

/-- **★ Inversion at the fst head.**  A union typing of an `fstCell`-headed subject is EXACTLY a
projection typing at the `gen_fst` row: for some second-component type `B`, the pair term is union-typed
at `product(C, B)` where `C` is the classifier, and the projected type is the first component (the
classifier).  No grown disjunct: `fstCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtFstHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = fstCell pairTerm) :
    ∃ secondType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell pinnedClassifier secondType) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨secondType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨secondType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.fstCellHasNoTyping (fun contra => contra)
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
  | elim ctx generator rule args params isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_fst` row survives (its member cell IS the fst cell);
      -- the other ten eliminator heads clash with the `fst` subject head.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natRec
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- idJ
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ fst — the SURVIVOR.  Destructure the child + params, recover the pair term from
      -- `subjectShape`, and surface the pair premise (typed at `product(firstType, secondType)`) from
      -- `premisesHold`; the projected first component IS the classifier (`outputType = firstType`).
      · match args, params with
        | .childCons _armPairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
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

/-! ## (1) Inversion at the snd head -/

/-- **★ Inversion at the snd head.**  A union typing of an `sndCell`-headed subject is EXACTLY a
projection typing at the `gen_snd` row: for some first-component type `A`, the pair term is union-typed
at `product(A, C)` where `C` is the classifier, and the projected type is the second component (the
classifier).  No grown disjunct: `sndCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtSndHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = sndCell pairTerm) :
    ∃ firstType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell firstType pinnedClassifier) ∧
      Conv pinnedClassifier classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨firstType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨firstType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.sndCellHasNoTyping (fun contra => contra)
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
  | elim ctx generator rule args params isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_snd` row survives (its member cell IS the snd cell);
      -- the other ten eliminator heads clash with the `snd` subject head.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natRec
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- idJ
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ snd — the SURVIVOR.  Destructure the child + params, recover the pair term from
      -- `subjectShape`, and surface the pair premise (typed at `product(firstType, secondType)`) from
      -- `premisesHold`; the projected second component IS the classifier (`outputType = secondType`).
      · match args, params with
        | .childCons _armPairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
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

end FX1Poly.Typed
