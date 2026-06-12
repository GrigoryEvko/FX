import FX1Poly.Typed.TableTypingUnionDivergence
import FX1Poly.Typed.HasTypeUnion

/-! # FX1Poly/Typed/UnionStaticTypingSoundness — the reserved-head refutation for the SINGLE union judgment

`StaticTypingSoundness.reservedHeadUntypedBySurvivingEngines` is the HON-5 honesty bundle for the
surviving standalone engines (grown + bridge): each disjunct says "a head the honesty classifier reports
reserved is untyped by THIS engine".  With the NATIVE-42/43 retirement collapsing the engine zoo into
`HasTypeUnion`, the honest statement collapses too: ONE lemma over the ONE judgment.  The classifier is `hasUnionEliminatorTypingRule` (`TableTypingUnionDivergence`) — the
full-union extension of the table classifier, which (unlike `hasSomeTypingRule`) tracks the three
union-only tables (`termIndexedFormerDescOf` / `nativeRecursiveElimRuleOf` / `listElimNativeRuleOf`).
Stating the refutation over the HONESTY classifier would be FALSE: the union types `natElim` / `natRec`
/ `listElim` / `idCode`-headed subjects, exactly the four strict-divergence witnesses — the pending
canonicity-collapse promotion decision stays untouched.

  * **`hasUnionEliminatorTypingRule_falsePeel`** — a union-reserved verdict forces all four disjuncts
    false (the propext-free `||`-peel, the union sibling of `hasTableTypingRule_falsePeel`).
  * **`hasSomeTypingRule_falseOfUnionReserved`** — union-reserved refines honesty-reserved (through the
    Leg-B equivalence), so the pre-union per-engine refutations remain applicable to the embeddings.
  * **`HasTypeUnion.reservedHeadUntyped`** (★) — the headline: a subject whose head the
    full-union classifier reports RESERVED is untyped by the union at EVERY context and classifier.
    Induction over the nineteen union arms: the four engine embeddings route through the shipped
    per-engine refutations (the term-indexed former inline — it predates no reserved lemma); each
    table-driven arm pins its generator by the table's `if`-chain, whereupon the subject's head
    computes LIVE, contradicting the verdict; the conv arm recurses (subject unchanged).
  * **`HasTypeUnion.headIsUnionLive`** (★) — the contrapositive consumer API: every union-typed
    subject's head is classifier-live.  This is the TRUTHFULNESS of `hasUnionEliminatorTypingRule`'s
    negative verdicts — `false` now means "the union types no such head", machine-checked, the exact
    property `hasSomeTypingRule` LOST when the union's recursive-eliminator arms landed.
  * Reserved-exemplar smoke: a `hilbertSpace`-headed subject is union-untypable.

## Zero-axiom

The peel reuses the propext-free `orEqFalse_leftFalse` / `orEqFalse_rightFalse`; the induction is
`by_cases` over decidable `Generator` equalities (instance-resolved, no `Classical`), `Option.some.inj`
on table hits, `if_neg` collapse on table misses, and `Bool.noConfusion` at the computed-live heads.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditUnionStaticTypingSoundness.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The union-classifier false-peel -/

/-- **A union-reserved verdict forces every disjunct false.**  The four-way conjunction peeled off
`hasUnionEliminatorTypingRule generator = false` via the propext-free `||`-projections: the table
classifier and the three union-only tables are all empty at the head. -/
theorem hasUnionEliminatorTypingRule_falsePeel {generator : Generator}
    (reserved : hasUnionEliminatorTypingRule generator = false) :
    hasTableTypingRule generator = false ∧
    (termIndexedFormerDescOf generator).isSome = false ∧
    (nativeRecursiveElimRuleOf generator).isSome = false ∧
    (listElimNativeRuleOf generator).isSome = false := by
  unfold hasUnionEliminatorTypingRule at reserved
  have peelThree := reserved
  have peelTwo := orEqFalse_leftFalse peelThree
  have peelOne := orEqFalse_leftFalse peelTwo
  exact ⟨orEqFalse_leftFalse peelOne, orEqFalse_rightFalse peelOne,
    orEqFalse_rightFalse peelTwo, orEqFalse_rightFalse peelThree⟩

/-- **Union-reserved refines honesty-reserved.**  A head the full-union classifier reports reserved is
reserved for the honesty classifier too (through the Leg-B equivalence
`hasSomeTypingRule_eq_hasTableTypingRule`), so the shipped pre-union per-engine refutations apply to
the union's engine embeddings unchanged. -/
theorem hasSomeTypingRule_falseOfUnionReserved {generator : Generator}
    (reserved : hasUnionEliminatorTypingRule generator = false) :
    hasSomeTypingRule generator = false := by
  rw [hasSomeTypingRule_eq_hasTableTypingRule]
  exact (hasUnionEliminatorTypingRule_falsePeel reserved).1

/-! ## ★ The union reserved-head refutation -/

/-- **★ A head the full-union classifier reports RESERVED is untyped by the union** — at every
context and every classifier.  The single-lemma successor of the HON-5 bundle
`reservedHeadUntypedBySurvivingEngines`: one judgment, one refutation.  Induction over the nineteen union
arms; every table-driven arm pins its generator through the table's `if`-chain and dies at the
computed-live head, the embeddings route through the per-engine refutations, the conv arm recurses. -/
theorem HasTypeUnion.reservedHeadUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (reserved : hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) = false) : False := by
  revert reserved
  induction typed with
  | ofGrown hostTyped =>
      intro reserved
      exact grownReservedUntyped (hasSomeTypingRule_falseOfUnionReserved reserved) hostTyped
  | baseTypeFormation context generator payload children rule isBaseType =>
      intro reserved
      have tableReserved := (hasUnionEliminatorTypingRule_falsePeel reserved).1
      have baseTableEmpty : (baseTypeRuleDescOf generator).isSome = false :=
        (hasTableTypingRule_falsePeel tableReserved).2.2.2.2.1
      rw [isBaseType] at baseTableEmpty
      exact Bool.noConfusion baseTableEmpty
  | dataIntroNullary context generator payload children rule isDataIntro =>
      intro reserved
      have tableReserved := (hasUnionEliminatorTypingRule_falsePeel reserved).1
      have dataTableEmpty : (dataIntroNullaryRuleDescOf generator).isSome = false :=
        (hasTableTypingRule_falsePeel tableReserved).2.2.2.2.2.1
      rw [isDataIntro] at dataTableEmpty
      exact Bool.noConfusion dataTableEmpty
  | flatFormation context generator payload children levels flag rule isFlatFormation premise =>
      intro reserved
      have tableReserved := (hasUnionEliminatorTypingRule_falsePeel reserved).1
      have flatTableEmpty : (flatTypingRuleDescOf generator).isSome = false :=
        (hasTableTypingRule_falsePeel tableReserved).2.2.2.1
      rw [isFlatFormation] at flatTableEmpty
      exact Bool.noConfusion flatTableEmpty
  | ofTermIndexedFormer formerTyped =>
      intro reserved
      cases formerTyped with
      | genFormation generator payload children carrier level flag rule
          isTermIndexed premises =>
          have formerTableEmpty : (termIndexedFormerDescOf generator).isSome = false :=
            (hasUnionEliminatorTypingRule_falsePeel reserved).2.1
          rw [isTermIndexed] at formerTableEmpty
          exact Bool.noConfusion formerTableEmpty
  | gradedBinderIntro context generator rule typeParamA typeParamB body domainLevel
      codomainLevel flag isIntro =>
      intro reserved
      by_cases isLam : generator = .gen_lam
      · subst isLam
        have ruleEq : lamGradedIntroRule = rule := Option.some.inj isIntro
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isPathLam : generator = .gen_pathLam
        · subst isPathLam
          have ruleEq : pathLamGradedIntroRule = rule := Option.some.inj isIntro
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [gradedIntroRuleOf] at isIntro
          rw [if_neg isLam, if_neg isPathLam] at isIntro
          cases isIntro
  | generalElim context generator rule typeParamA typeParamB typeParamC typeParamD
      eliminated argument isElim =>
      intro reserved
      by_cases isApp : generator = .gen_app
      · subst isApp
        have ruleEq : appGeneralElimRule = rule := Option.some.inj isElim
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isPathApp : generator = .gen_pathApp
        · subst isPathApp
          have ruleEq : pathAppGeneralElimRule = rule := Option.some.inj isElim
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [generalElimRuleOf] at isElim
          rw [if_neg isApp, if_neg isPathApp] at isElim
          cases isElim
  | recursiveElim context generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim =>
      intro reserved
      by_cases isNatElim : generator = .gen_natElim
      · subst isNatElim
        have ruleEq : natElimNativeRecursiveRule = rule := Option.some.inj isRecursiveElim
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isNatRec : generator = .gen_natRec
        · subst isNatRec
          have ruleEq : natRecNativeRecursiveRule = rule := Option.some.inj isRecursiveElim
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [nativeRecursiveElimRuleOf] at isRecursiveElim
          rw [if_neg isNatElim, if_neg isNatRec] at isRecursiveElim
          cases isRecursiveElim
  | twoBranchMatchElim context generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch =>
      intro reserved
      by_cases isBoolElim : generator = .gen_boolElim
      · subst isBoolElim
        have ruleEq : boolElimNativeMatchRule = rule := Option.some.inj isTwoBranchMatch
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isOptionMatch : generator = .gen_optionMatch
        · subst isOptionMatch
          have ruleEq : optionMatchNativeMatchRule = rule := Option.some.inj isTwoBranchMatch
          subst ruleEq
          exact Bool.noConfusion reserved
        · by_cases isEitherMatch : generator = .gen_eitherMatch
          · subst isEitherMatch
            have ruleEq : eitherMatchNativeMatchRule = rule := Option.some.inj isTwoBranchMatch
            subst ruleEq
            exact Bool.noConfusion reserved
          · dsimp only [nativeTwoBranchMatchRuleOf] at isTwoBranchMatch
            rw [if_neg isBoolElim, if_neg isOptionMatch, if_neg isEitherMatch]
              at isTwoBranchMatch
            cases isTwoBranchMatch
  | pathInductionElim context generator rule motive baseCase witness typeCode endpoint
      resultType isPathInduction =>
      intro reserved
      by_cases isIdJ : generator = .gen_idJ
      · subst isIdJ
        have ruleEq : idJNativePathInductionRule = rule := Option.some.inj isPathInduction
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativePathInductionRuleOf] at isPathInduction
        rw [if_neg isIdJ] at isPathInduction
        cases isPathInduction
  | projectionElim context generator rule pairTerm firstType secondType isProjection =>
      intro reserved
      by_cases isFst : generator = .gen_fst
      · subst isFst
        have ruleEq : fstNativeProjectionRule = rule := Option.some.inj isProjection
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isSnd : generator = .gen_snd
        · subst isSnd
          have ruleEq : sndNativeProjectionRule = rule := Option.some.inj isProjection
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [nativeProjectionRuleOf] at isProjection
          rw [if_neg isFst, if_neg isSnd] at isProjection
          cases isProjection
  | recursiveUnaryIntro context generator rule child isRecursiveUnary =>
      intro reserved
      by_cases isNatSucc : generator = .gen_natSucc
      · subst isNatSucc
        have ruleEq : natSuccNativeRecursiveUnaryRule = rule := Option.some.inj isRecursiveUnary
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativeRecursiveUnaryDataIntroRuleOf] at isRecursiveUnary
        rw [if_neg isNatSucc] at isRecursiveUnary
        cases isRecursiveUnary
  | recursiveBinaryIntro context generator rule head tail elementType isRecursiveBinary =>
      intro reserved
      by_cases isListCons : generator = .gen_listCons
      · subst isListCons
        have ruleEq : listConsNativeRecursiveBinaryRule = rule :=
          Option.some.inj isRecursiveBinary
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativeRecursiveBinaryDataIntroRuleOf] at isRecursiveBinary
        rw [if_neg isListCons] at isRecursiveBinary
        cases isRecursiveBinary
  | pinnedUnaryIntro context generator rule child elementType isPinnedUnary =>
      intro reserved
      by_cases isOptionSome : generator = .gen_optionSome
      · subst isOptionSome
        have ruleEq : optionSomeNativePinnedUnaryRule = rule := Option.some.inj isPinnedUnary
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativePinnedUnaryDataIntroRuleOf] at isPinnedUnary
        rw [if_neg isOptionSome] at isPinnedUnary
        cases isPinnedUnary
  | nullaryFreeTypeIntro context generator rule elementType elementLevel flag
      isNullaryFreeType =>
      intro reserved
      by_cases isOptionNone : generator = .gen_optionNone
      · subst isOptionNone
        have ruleEq : optionNoneNativeNullaryFreeTypeRule = rule :=
          Option.some.inj isNullaryFreeType
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isListNil : generator = .gen_listNil
        · subst isListNil
          have ruleEq : listNilNativeNullaryFreeTypeRule = rule :=
            Option.some.inj isNullaryFreeType
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [nativeNullaryFreeTypeDataIntroRuleOf] at isNullaryFreeType
          rw [if_neg isOptionNone, if_neg isListNil] at isNullaryFreeType
          cases isNullaryFreeType
  | coproductIntro context generator rule value pinnedType freeType freeLevel flag
      isCoproduct =>
      intro reserved
      by_cases isEitherInl : generator = .gen_eitherInl
      · subst isEitherInl
        have ruleEq : eitherInlNativeCoproductRule = rule := Option.some.inj isCoproduct
        subst ruleEq
        exact Bool.noConfusion reserved
      · by_cases isEitherInr : generator = .gen_eitherInr
        · subst isEitherInr
          have ruleEq : eitherInrNativeCoproductRule = rule := Option.some.inj isCoproduct
          subst ruleEq
          exact Bool.noConfusion reserved
        · dsimp only [nativeCoproductDataIntroRuleOf] at isCoproduct
          rw [if_neg isEitherInl, if_neg isEitherInr] at isCoproduct
          cases isCoproduct
  | nonDependentBinaryIntro context generator rule firstChild secondChild firstType
      secondType isNonDependentBinary =>
      intro reserved
      by_cases isPair : generator = .gen_pair
      · subst isPair
        have ruleEq : pairNativeNonDependentBinaryRule = rule :=
          Option.some.inj isNonDependentBinary
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativeNonDependentBinaryDataIntroRuleOf] at isNonDependentBinary
        rw [if_neg isPair] at isNonDependentBinary
        cases isNonDependentBinary
  | reflexiveIntro context generator rule witness witnessType isReflexive =>
      intro reserved
      by_cases isRefl : generator = .gen_refl
      · subst isRefl
        have ruleEq : reflNativeReflexiveRule = rule := Option.some.inj isReflexive
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [nativeReflexiveDataIntroRuleOf] at isReflexive
        rw [if_neg isRefl] at isReflexive
        cases isReflexive
  | listElim context generator rule motive scrutinee nilBranch consBranch elementType
      resultType isListElim =>
      intro reserved
      by_cases isListElimHead : generator = .gen_listElim
      · subst isListElimHead
        have ruleEq : listElimNativeRule = rule := Option.some.inj isListElim
        subst ruleEq
        exact Bool.noConfusion reserved
      · dsimp only [listElimNativeRuleOf] at isListElim
        rw [if_neg isListElimHead] at isListElim
        cases isListElim
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      exact typedIH

/-! ## ★ The contrapositive consumer API -/

/-- **★ Every union-typed subject's head is classifier-LIVE.**  The contrapositive of
`reservedHeadUntyped`: `hasUnionEliminatorTypingRule`'s negative verdicts are TRUTHFUL about the union
— `false` means "the union types no subject with this head", the exact property the honesty classifier
lost when the union's recursive-eliminator arms and the Id retrofit landed. -/
theorem HasTypeUnion.headIsUnionLive {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier) :
    hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) = true := by
  cases liveVerdict : hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) with
  | true => rfl
  | false => exact (typed.reservedHeadUntyped liveVerdict).elim

/-! ## Reserved-exemplar smoke -/

/-- The tier-★ extension name stays reserved under the FULL-union classifier (not just the honesty
classifier) — the union tables carry no `hilbertSpace` row. -/
theorem hasUnionEliminatorTypingRule_hilbertSpace :
    hasUnionEliminatorTypingRule .gen_hilbertSpace = false := rfl

/-- **A `hilbertSpace`-headed subject is union-untypable** — the reserved-exemplar instantiation of
the headline refutation. -/
theorem HasTypeUnion.hilbertSpaceHeadUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (headIsHilbert : RawTerm.headGenerator subject = .gen_hilbertSpace)
    (typed : HasTypeUnion profile context subject classifier) : False :=
  typed.reservedHeadUntyped
    (by rw [headIsHilbert]; exact hasUnionEliminatorTypingRule_hilbertSpace)

end FX1Poly.Typed
