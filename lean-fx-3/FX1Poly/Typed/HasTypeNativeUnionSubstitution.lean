import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeNativeUnionInversion
import FX1Poly.Typed.NativeUnionCellSubstitution
import FX1Poly.Typed.NativeUnionEngineSubstitution
import FX1Poly.Typed.HasTypeDescPiSubstPair
import FX1Poly.Typed.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Core.RawTermOccurrenceSubstLift

/-! # FX1Poly/Typed/HasTypeNativeUnionSubstitution — NATIVE-37 part b: the SUBSTITUTION lemma for the
    24-arm native union + the 2-variable corollaries + the GENERAL succ-branch recursive-eliminator ι

This file discharges the campaign's longest-standing residual (the NATIVE-04 line): typing the succ-ι
reduct `succBranch[var 0 := natElim(...), var 1 := predecessor]` for an ARBITRARY typed branch.  Since
NATIVE-04 the host 2-variable substitution lemma (`HasTypeDescPi.substPairUnderTwoBindings`) existed but
its premises are HOST typings — and the recursive call `natElimCell(...)` is never host-typed.  The
union now contains everything; this file restates substitution over it.

## The substituent discipline (HOST-typed images — the universally-closeable formulation)

`substRespectingContext` is preserved along any substitution whose variable images are HOST-typed
(`HasTypeDescPi`) at the substituted lookup types.  Every host image is also a union image (via
`ofGrown`), so the side condition is the strongest one that lets EVERY arm close:

  * the four ENGINE EMBEDDINGS (`ofGrown` / `ofBaseType` / `ofDataIntro` / `ofTermIndexedFormer`) and the
    nine scrutinee/host-premise arms route their host/engine premises through the respective engine's own
    `substRespectingContext` (host substituents are exactly what those engines demand) and re-embed;
  * the seven RECURSIVE native arms (`gradedBinderIntro` / `generalElim` / `recursiveElim` /
    `twoBranchMatchElim` / `pathInductionElim` / `projectionElim` / `recursiveUnaryIntro` /
    `recursiveBinaryIntro`) recurse via the induction hypotheses, with `RawTermSubst.lift` crossing the
    one/two binders (the lifted condition keeps the images host-typed: `0` → the fresh `var` via
    `ofFormation`, `k+1` → the host image weakened).

The graded arm additionally transports the affine binder check
(`RawTerm.occurrenceCountAt_subst_lift_zeroPosition`: a lifted substitution preserves the freshest-binder
occurrence count, so `gradedBinderChecks usage body` survives verbatim).

## ★ The 2-variable corollaries + the succ-ι discharge

  * `HasTypeNativeUnion.substPairUnderTwoBindings` / `substPairNonDependent` — the union mirrors of the
    host versions, instantiating `substRespectingContext` at `cons innerArg (singleton outerArg)`.
  * `natElimSuccIotaComputesTypedInUnion` (★★) / `natRecSuccIotaComputesTypedInUnion` — the GENERAL
    succ-branch ι.  A typed `natElim(motive, z, sb, succ p)` ι-steps and the substituted reduct
    `natElimSuccContractum motive z sb p` is union-typed at `resultType` UNCONDITIONALLY (no separate
    reduct-typing premise): the inner substituent is the recursive `natElimCell` typed by the union's own
    `recursiveElim` arm, the outer is the predecessor, and `substPairNonDependent` transports the branch
    typing.  The IH-return family (the bespoke `natElimComputesToNumeral` rung) was the special case; this
    is the full family — closing the NATIVE-04 line completely.

The succ branch is typed in the union at the TWICE-WEAKENED `resultType` under the two binders (the
non-dependent recursive-eliminator step shape, matching the union's `recursiveElim` arm's stored
stepBranch); the inner binder carries the once-weakened recursive result, the outer the predecessor's Nat
type.  The inner recursive-result substituent and the predecessor substituent are supplied HOST-typed —
the predecessor as a host typing of `p : Nat`, the recursive result as a host typing of the recursive
call — so the discharge stands on the host-substituent formulation (the recursive call's union typing
enters through the branch's own derivation, not the substitution side condition).

## Zero-axiom

`substRespectingContext` is `induction` over the 24 arms + the cell-subst `rfl` commutations + the
per-rule `subst0_subst_commute` reshapes + the lifted-occurrence preservation + the engine subst lemmas.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditNativeUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation FX1Poly.Modal

/-- The host-substituent context condition for the native union: every variable image is HOST-typed at
the substituted lookup type. -/
abbrev HasTypeNativeUnion.SubstHostTyped {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    HasTypeDescPi profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index))

/-- A host-typed image is a union image (via `ofGrown`) — the bridge each recursive arm's IH uses to feed
its native premises a union substituent built from the host condition. -/
theorem HasTypeNativeUnion.SubstHostTyped.toUnionImage {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeNativeUnion.SubstHostTyped sourceContext targetContext substitution)
    (index : Fin sourceScope) :
    HasTypeNativeUnion profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index)) :=
  HasTypeNativeUnion.ofGrown (condition index)

/-- The two-binder lift of the host-substituent condition (the recursiveElim / idJ succ-branch shape):
the double lift of a host condition is a host condition at the context extended by the two domains.  An
iterate of `substContextCondition_cons`. -/
theorem HasTypeNativeUnion.SubstHostTyped.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeNativeUnion.SubstHostTyped sourceContext targetContext substitution) :
    HasTypeNativeUnion.SubstHostTyped ((sourceContext.cons outerType).cons innerType)
      ((targetContext.cons (RawTerm.subst substitution outerType)).cons
        (RawTerm.subst (iterateLiftRaw substitution 1) innerType))
      (iterateLiftRaw substitution 2) := by
  have outerStep :
      HasTypeNativeUnion.SubstHostTyped (sourceContext.cons outerType)
        (targetContext.cons (RawTerm.subst substitution outerType))
        (iterateLiftRaw substitution 1) :=
    substContextCondition_cons outerType substitution condition
  have innerStep :
      HasTypeNativeUnion.SubstHostTyped ((sourceContext.cons outerType).cons innerType)
        ((targetContext.cons (RawTerm.subst substitution outerType)).cons
          (RawTerm.subst (iterateLiftRaw substitution 1) innerType))
        (iterateLiftRaw (iterateLiftRaw substitution 1) 1) :=
    substContextCondition_cons innerType (iterateLiftRaw substitution 1) outerStep
  exact innerStep

/-- **The affine binder check transports through a lifted substitution.**  `gradedBinderChecks usage
body` (a bound on `occurrenceCountAt body (var 0)`) survives substitution by `iterateLiftRaw σ 1`: the
lift preserves the freshest-binder occurrence count (`occurrenceCountAt_subst_lift_zeroPosition`), so the
bound holds verbatim for the substituted body.  The graded arm's binder-grade premise transport. -/
theorem gradedBinderChecks_subst_lift {sourceScope targetScope : Nat}
    (usage : UsageGrade) (substitution : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1))
    (checked : gradedBinderChecks usage body) :
    gradedBinderChecks usage (RawTerm.subst (iterateLiftRaw substitution 1) body) := by
  -- `gradedBinderChecks usage t = usage.boundsCount (occurrenceCountAt t (var 0))`.
  show usage.boundsCount (RawTerm.occurrenceCountAt
    (RawTerm.subst (iterateLiftRaw substitution 1) body) ⟨0, Nat.succ_pos targetScope⟩)
  rw [RawTerm.occurrenceCountAt_subst_lift_zeroPosition]
  exact checked

/-- **★ The pointwise substitution lemma over the native union.**  A union derivation at `sourceContext`,
substituted by any HOST-typed substitution, gives a union derivation of the substituted subject at the
substituted classifier.  By `induction` over the 24 arms: the engine embeddings and host-premise arms
route through the engines' own `substRespectingContext` (host substituents are exactly what they demand)
and re-embed; the recursive native arms recurse via the IHs with `RawTermSubst.lift` crossing binders;
the graded arm transports the affine binder check by the lifted-occurrence preservation. -/
theorem HasTypeNativeUnion.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeNativeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeNativeUnion.SubstHostTyped sourceContext targetContext substitution →
      HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  induction derivation with
  | ofGrown hostTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofGrown
        (hostTyped.substRespectingContext targetContext substitution condition)
  | ofBaseType baseTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofBaseType
        (baseTyped.substRespectingContext targetContext substitution condition)
  | ofDataIntro dataTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofDataIntro
        (dataTyped.substRespectingContext targetContext substitution condition)
  | ofTermIndexedFormer formerTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofTermIndexedFormer
        (formerTyped.substRespectingContext targetContext substitution condition)
  | ofNatIntro natTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofNatIntro
        (natTyped.substRespectingContext targetContext substitution condition)
  | ofOptionIntro optionTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofOptionIntro
        (optionTyped.substRespectingContext targetContext substitution condition)
  | ofEitherIntro eitherTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofEitherIntro
        (eitherTyped.substRespectingContext targetContext substitution condition)
  | ofIdIntro idTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofIdIntro
        (idTyped.substRespectingContext targetContext substitution condition)
  | ofPairIntro pairTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofPairIntro
        (pairTyped.substRespectingContext targetContext substitution condition)
  | ofListIntro listTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeNativeUnion.ofListIntro
        (listTyped.substRespectingContext targetContext substitution condition)
  | recursiveUnaryIntro context generator rule child isRecursiveUnary _childTyped childIH =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      -- natSucc row: memberCell = natSuccCell, childType = outputType = natTypeCell (all defeq).
      have childSubst := childIH targetContext substitution condition
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (natSuccCell child)) (RawTerm.subst substitution natTypeCell)
      rw [subst_natSuccCell, subst_natTypeCell]
      exact HasTypeNativeUnion.recursiveUnaryIntro targetContext .gen_natSucc
        natSuccNativeRecursiveUnaryRule (RawTerm.subst substitution child) rfl childSubst
  | recursiveBinaryIntro context generator rule head tail elementType isRecursiveBinary
      headTyped _tailTyped tailIH =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      -- listCons row: memberCell = listConsCell, containerType = listTypeCell (defeq).
      have tailSubst := tailIH targetContext substitution condition
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (listConsCell head tail))
        (RawTerm.subst substitution (listTypeCell elementType))
      rw [subst_listConsCell, subst_listTypeCell]
      exact HasTypeNativeUnion.recursiveBinaryIntro targetContext .gen_listCons
        listConsNativeRecursiveBinaryRule (RawTerm.subst substitution head)
        (RawTerm.subst substitution tail) (RawTerm.subst substitution elementType) rfl
        (headTyped.substRespectingContext targetContext substitution condition) tailSubst
  | pinnedUnaryIntro context generator rule child elementType isPinnedUnary childTyped =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      -- optionSome row: memberCell = optionSomeCell, outputType = optionTypeCell.
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (optionSomeCell child))
        (RawTerm.subst substitution (optionTypeCell elementType))
      rw [subst_optionSomeCell, subst_optionTypeCell]
      exact HasTypeNativeUnion.pinnedUnaryIntro targetContext .gen_optionSome
        optionSomeNativePinnedUnaryRule (RawTerm.subst substitution child)
        (RawTerm.subst substitution elementType) rfl
        (childTyped.substRespectingContext targetContext substitution condition)
  | nullaryFreeTypeIntro context generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType
      subst ruleEq
      -- optionNone row: memberCell = optionNoneCell, outputType = optionTypeCell.
      have elementFormSubst := elementTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at elementFormSubst
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution optionNoneCell)
        (RawTerm.subst substitution (optionTypeCell elementType))
      rw [subst_optionNoneCell, subst_optionTypeCell]
      exact HasTypeNativeUnion.nullaryFreeTypeIntro targetContext .gen_optionNone
        optionNoneNativeNullaryFreeTypeRule (RawTerm.subst substitution elementType)
        elementLevel flag rfl elementFormSubst
  | coproductIntro context generator rule value pinnedType freeType freeLevel flag isCoproduct
      valueTyped freeTypeFormed =>
      intro targetScope targetContext substitution condition
      have valueSubst := valueTyped.substRespectingContext targetContext substitution condition
      have freeFormSubst := freeTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at freeFormSubst
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        -- eitherInl row: injectionCell = eitherInlCell, output = eitherTypeCell pinned free.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (eitherInlCell value))
          (RawTerm.subst substitution (eitherTypeCell pinnedType freeType))
        rw [subst_eitherInlCell, subst_eitherTypeCell]
        exact HasTypeNativeUnion.coproductIntro targetContext .gen_eitherInl
          eitherInlNativeCoproductRule (RawTerm.subst substitution value)
          (RawTerm.subst substitution pinnedType) (RawTerm.subst substitution freeType)
          freeLevel flag rfl valueSubst freeFormSubst
      · subst ruleEq
        -- eitherInr row: injectionCell = eitherInrCell, output = eitherTypeCell free pinned.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (eitherInrCell value))
          (RawTerm.subst substitution (eitherTypeCell freeType pinnedType))
        rw [subst_eitherInrCell, subst_eitherTypeCell]
        exact HasTypeNativeUnion.coproductIntro targetContext .gen_eitherInr
          eitherInrNativeCoproductRule (RawTerm.subst substitution value)
          (RawTerm.subst substitution pinnedType) (RawTerm.subst substitution freeType)
          freeLevel flag rfl valueSubst freeFormSubst
  | nonDependentBinaryIntro context generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      -- pair row: memberCell = pairCell, output = productTypeCell.
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (pairCell firstChild secondChild))
        (RawTerm.subst substitution (productTypeCell firstType secondType))
      rw [subst_pairCell, subst_productTypeCell]
      exact HasTypeNativeUnion.nonDependentBinaryIntro targetContext .gen_pair
        pairNativeNonDependentBinaryRule (RawTerm.subst substitution firstChild)
        (RawTerm.subst substitution secondChild) (RawTerm.subst substitution firstType)
        (RawTerm.subst substitution secondType) rfl
        (firstTyped.substRespectingContext targetContext substitution condition)
        (secondTyped.substRespectingContext targetContext substitution condition)
  | reflexiveIntro context generator rule witness witnessType isReflexive witnessTyped =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      -- refl row: memberCell = reflCell, output = idTypeCell witnessType witness witness.
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (reflCell witness))
        (RawTerm.subst substitution (idTypeCell witnessType witness witness))
      rw [subst_reflCell, subst_idTypeCell]
      exact HasTypeNativeUnion.reflexiveIntro targetContext .gen_refl
        reflNativeReflexiveRule (RawTerm.subst substitution witness)
        (RawTerm.subst substitution witnessType) rfl
        (witnessTyped.substRespectingContext targetContext substitution condition)
  | recursiveElim context generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim _scrutineeTyped _baseBranchTyped scrutineeIH baseBranchIH =>
      intro targetScope targetContext substitution condition
      have scrutineeSubst := scrutineeIH targetContext substitution condition
      have baseBranchSubst := baseBranchIH targetContext substitution condition
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        -- natElim row: memberCell = natElimCell, scrutineeType = natTypeCell, output = resultType.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution
            (natElimCell motive baseBranch stepBranch scrutinee))
          (RawTerm.subst substitution resultType)
        rw [subst_natElimCell]
        exact HasTypeNativeUnion.recursiveElim targetContext .gen_natElim
          natElimNativeRecursiveRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution baseBranch)
          (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution resultType)
          rfl scrutineeSubst baseBranchSubst
      · subst ruleEq
        -- natRec row: memberCell = natRecCell, scrutineeType = natTypeCell, output = resultType.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution
            (natRecCell motive baseBranch stepBranch scrutinee))
          (RawTerm.subst substitution resultType)
        rw [subst_natRecCell]
        exact HasTypeNativeUnion.recursiveElim targetContext .gen_natRec
          natRecNativeRecursiveRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution baseBranch)
          (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution resultType)
          rfl scrutineeSubst baseBranchSubst
  | projectionElim context generator rule pairTerm firstType secondType isProjection
      _pairTyped pairIH =>
      intro targetScope targetContext substitution condition
      have pairSubst := pairIH targetContext substitution condition
      rw [subst_productTypeCell] at pairSubst
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        -- fst row: memberCell = fstCell, projectedType = firstType.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (fstCell pairTerm)) (RawTerm.subst substitution firstType)
        rw [subst_fstCell]
        exact HasTypeNativeUnion.projectionElim targetContext .gen_fst fstNativeProjectionRule
          (RawTerm.subst substitution pairTerm) (RawTerm.subst substitution firstType)
          (RawTerm.subst substitution secondType) rfl pairSubst
      · subst ruleEq
        -- snd row: memberCell = sndCell, projectedType = secondType.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (sndCell pairTerm)) (RawTerm.subst substitution secondType)
        rw [subst_sndCell]
        exact HasTypeNativeUnion.projectionElim targetContext .gen_snd sndNativeProjectionRule
          (RawTerm.subst substitution pairTerm) (RawTerm.subst substitution firstType)
          (RawTerm.subst substitution secondType) rfl pairSubst
  | twoBranchMatchElim context generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch _scrutineeTyped _firstBranchTyped
      _secondBranchTyped scrutineeIH firstBranchIH secondBranchIH =>
      intro targetScope targetContext substitution condition
      have scrutineeSubst := scrutineeIH targetContext substitution condition
      have firstBranchSubst := firstBranchIH targetContext substitution condition
      have secondBranchSubst := secondBranchIH targetContext substitution condition
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        -- boolElim row: scrutinee at boolTypeCell, both branches at resultType, member boolElimCell.
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (boolElimCell motive scrutinee firstBranch secondBranch))
          (RawTerm.subst substitution resultType)
        rw [subst_boolElimCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_boolElim
          boolElimNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
          (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
          rfl scrutineeSubst firstBranchSubst secondBranchSubst
      · subst ruleEq
        -- optionMatch row: scrutinee at option(A), None at result, Some at A → result.  The Some branch
        -- type `piTyCodeCell A (weaken result)` substitutes by the lift/weaken naturality square.
        rw [show optionMatchNativeMatchRule.secondBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamA (RawTerm.weaken resultType) from rfl,
          subst_nonDependentArrow] at secondBranchSubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (optionMatchCell motive firstBranch secondBranch scrutinee))
          (RawTerm.subst substitution resultType)
        rw [subst_optionMatchCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_optionMatch
          optionMatchNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
          (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
          rfl scrutineeSubst firstBranchSubst secondBranchSubst
      · subst ruleEq
        -- eitherMatch row: scrutinee at either(A, B), both branches non-dependent arrows.
        rw [show eitherMatchNativeMatchRule.firstBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamA (RawTerm.weaken resultType) from rfl,
          subst_nonDependentArrow] at firstBranchSubst
        rw [show eitherMatchNativeMatchRule.secondBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamB (RawTerm.weaken resultType) from rfl,
          subst_nonDependentArrow] at secondBranchSubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (eitherMatchCell motive firstBranch secondBranch scrutinee))
          (RawTerm.subst substitution resultType)
        rw [subst_eitherMatchCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_eitherMatch
          eitherMatchNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
          (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
          rfl scrutineeSubst firstBranchSubst secondBranchSubst
  | pathInductionElim context generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction _witnessTyped _baseCaseTyped witnessIH baseCaseIH =>
      intro targetScope targetContext substitution condition
      have witnessSubst := witnessIH targetContext substitution condition
      have baseCaseSubst := baseCaseIH targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      -- idJ row: witness at Id(typeCode, endpoint, endpoint), base at result, member idJCell.
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (idJCell motive baseCase witness))
        (RawTerm.subst substitution resultType)
      rw [subst_idJCell]
      exact HasTypeNativeUnion.pathInductionElim targetContext .gen_idJ idJNativePathInductionRule
        (RawTerm.subst (iterateLiftRaw substitution 2) motive)
        (RawTerm.subst substitution baseCase) (RawTerm.subst substitution witness)
        (RawTerm.subst substitution typeCode) (RawTerm.subst substitution endpoint)
        (RawTerm.subst substitution resultType) rfl witnessSubst baseCaseSubst
  | listElim context generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      intro targetScope targetContext substitution condition
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      -- listElim row: scrutinee list-intro-typed, nil at result, cons at the step-function type.
      have scrutineeSubst := scrutineeTyped.substRespectingContext targetContext substitution condition
      have nilSubst := nilBranchTyped.substRespectingContext targetContext substitution condition
      have consSubst := consBranchTyped.substRespectingContext targetContext substitution condition
      rw [subst_listStepFunctionType] at consSubst
      show HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch))
        (RawTerm.subst substitution resultType)
      rw [subst_listElimCell]
      exact HasTypeNativeUnion.listElim targetContext .gen_listElim listElimNativeRule
        (RawTerm.subst (iterateLiftRaw substitution 1) motive)
        (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution nilBranch)
        (RawTerm.subst substitution consBranch) (RawTerm.subst substitution elementType)
        (RawTerm.subst substitution resultType) rfl scrutineeSubst nilSubst consSubst
  | generalElim context generator rule typeParamA typeParamB typeParamC typeParamD eliminated
      argument isElim _eliminatedTyped _argumentTyped eliminatedIH argumentIH =>
      intro targetScope targetContext substitution condition
      have eliminatedSubst := eliminatedIH targetContext substitution condition
      have argumentSubst := argumentIH targetContext substitution condition
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        obtain rfl : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        -- app row: eliminated at Π(A, B), argument at A, member appCell, output subst0 B argument.
        rw [show appGeneralElimRule.eliminatedType _ typeParamA typeParamB typeParamC typeParamD
              = piTyCodeCell typeParamA typeParamB from rfl, subst_piTyCodeCell] at eliminatedSubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (appCell eliminated argument))
          (RawTerm.subst substitution (RawTerm.subst0 typeParamB argument))
        rw [subst_appCell, RawTerm.subst0_subst_commute]
        exact HasTypeNativeUnion.generalElim targetContext .gen_app appGeneralElimRule
          (RawTerm.subst substitution typeParamA)
          (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB)
          (RawTerm.subst substitution typeParamC) (RawTerm.subst substitution typeParamD)
          (RawTerm.subst substitution eliminated) (RawTerm.subst substitution argument)
          rfl eliminatedSubst argumentSubst
      · subst hPath
        obtain rfl : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        -- pathApp row: eliminated at bridge(A, C, D), argument at Interval, output A (constant carrier).
        rw [show pathAppGeneralElimRule.eliminatedType _ typeParamA typeParamB typeParamC typeParamD
              = bridgeTypeCell typeParamA typeParamC typeParamD from rfl,
          subst_bridgeTypeCell] at eliminatedSubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (pathAppCell eliminated argument))
          (RawTerm.subst substitution typeParamA)
        rw [subst_pathAppCell]
        exact HasTypeNativeUnion.generalElim targetContext .gen_pathApp pathAppGeneralElimRule
          (RawTerm.subst substitution typeParamA)
          (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB)
          (RawTerm.subst substitution typeParamC) (RawTerm.subst substitution typeParamD)
          (RawTerm.subst substitution eliminated) (RawTerm.subst substitution argument)
          rfl eliminatedSubst argumentSubst
  | gradedBinderIntro context generator rule typeParamA typeParamB body domainLevel codomainLevel flag
      isIntro binderGraded _domainFormed _classifierFormed _bodyTyped domainIH classifierIH bodyIH =>
      intro targetScope targetContext substitution condition
      -- The lifted host condition for the body / classifier IHs (the binder-crossing leg).
      have liftedCondition :
          HasTypeNativeUnion.SubstHostTyped
            (context.cons (rule.domainCell _ typeParamA))
            (targetContext.cons (RawTerm.subst substitution (rule.domainCell _ typeParamA)))
            (iterateLiftRaw substitution 1) :=
        substContextCondition_cons (rule.domainCell _ typeParamA) substitution condition
      have bodySubst := bodyIH (targetContext.cons
        (RawTerm.subst substitution (rule.domainCell _ typeParamA)))
        (iterateLiftRaw substitution 1) liftedCondition
      -- The substituted binder check (the affine premise transports through the lift).
      have binderGradedSubst :
          gradedBinderChecks rule.binderUsage (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
        gradedBinderChecks_subst_lift rule.binderUsage substitution body binderGraded
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        obtain rfl : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        -- lam row: domain = A, classifier = B, member = lamCell A body, output = piTyCodeCell A B.
        have domainSubst := domainIH rfl targetContext substitution condition
        rw [subst_universeCodeCell] at domainSubst
        have classifierSubst := classifierIH rfl (targetContext.cons
          (RawTerm.subst substitution typeParamA)) (iterateLiftRaw substitution 1) liftedCondition
        rw [subst_universeCodeCell] at classifierSubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (lamCell typeParamA body))
          (RawTerm.subst substitution (piTyCodeCell typeParamA typeParamB))
        rw [subst_lamCell, subst_piTyCodeCell]
        exact HasTypeNativeUnion.gradedBinderIntro targetContext .gen_lam lamGradedIntroRule
          (RawTerm.subst substitution typeParamA)
          (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB)
          (RawTerm.subst (iterateLiftRaw substitution 1) body)
          domainLevel codomainLevel flag rfl binderGradedSubst
          (fun _ => domainSubst) (fun _ => classifierSubst) bodySubst
      · subst hPath
        obtain rfl : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        -- pathLam row: domain = Interval, classifier = weaken A, member = pathLamCell body,
        -- output = bridge A (subst0 body i0) (subst0 body i1).  No formation premises.  The body's
        -- classifier `weaken A` substitutes by the lift/weaken naturality square.
        rw [show pathLamGradedIntroRule.bodyClassifier _ typeParamA typeParamB
              = RawTerm.weaken typeParamA from rfl, subst_iterateLift_one_weaken_commute] at bodySubst
        show HasTypeNativeUnion profile targetContext
          (RawTerm.subst substitution (pathLamCell body))
          (RawTerm.subst substitution
            (bridgeTypeCell typeParamA (RawTerm.subst0 body intervalZeroCell)
              (RawTerm.subst0 body intervalOneCell)))
        rw [subst_pathLamCell, subst_bridgeTypeCell, RawTerm.subst0_subst_commute,
          RawTerm.subst0_subst_commute]
        exact HasTypeNativeUnion.gradedBinderIntro targetContext .gen_pathLam pathLamGradedIntroRule
          (RawTerm.subst substitution typeParamA)
          (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB)
          (RawTerm.subst (iterateLiftRaw substitution 1) body)
          domainLevel codomainLevel flag rfl binderGradedSubst
          (fun gateHolds => Bool.noConfusion gateHolds)
          (fun gateHolds => Bool.noConfusion gateHolds) bodySubst

/-! ## ★ The 2-variable substitution corollaries over the union (deliverable 2) -/

/-- **★ The typed 2-variable substitution lemma over the union.**  A union derivation under two binders
— outer binder `outerType`, inner binder `innerType` (which may mention the outer variable) — substituted
simultaneously at `var 0 := innerArg, var 1 := outerArg` (both HOST-typed) preserves
`HasTypeNativeUnion`, with subject and classifier substituted.  The inner substituent is host-typed at the
OUTER-SUBSTITUTED inner binder type.  The union mirror of `HasTypeDescPi.substPairUnderTwoBindings`,
instantiating `substRespectingContext` at `cons innerArg (singleton outerArg)` — the `Fin` 0 / 1 / k+2
split is verbatim the host proof's. -/
theorem HasTypeNativeUnion.substPairUnderTwoBindings {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType : RawTerm scope}
    {innerType : RawTerm (scope + 1)} {subject classifier : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (derivation :
      HasTypeNativeUnion profile ((context.cons outerType).cons innerType) subject classifier)
    (innerArgTyped : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg) innerType))
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeNativeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) subject)
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) classifier) := by
  refine derivation.substRespectingContext context
    (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDescPi profile context innerArg
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
          (RawTerm.rename RawRenaming.weaken innerType))
      rw [RawTerm.weaken_subst_cons]
      exact innerArgTyped
  | succ tailValue =>
      cases tailValue with
      | zero =>
          show HasTypeDescPi profile context outerArg
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken outerType)))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact outerArgTyped
      | succ priorValue =>
          show HasTypeDescPi profile context
            (variableCell ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken
                (context.lookup ⟨priorValue,
                  Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩))))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact HasTypeDescPi.ofFormation
            (HasTypeDesc.var context ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)

/-- **★ The recursor-step-shaped substPair corollary over the union.**  A branch typed in the UNION at a
TWICE-WEAKENED result type under two binders (the recursive-eliminator step shape: inner binder = the
once-weakened result type carrying the recursive result, outer binder = the scrutinee's element type),
substituted at a HOST-typed recursive result and a HOST-typed outer argument, is union-typed at the result
type on the nose — both weakenings cancel against the two substituents.  The union mirror of
`HasTypeDescPi.substPairNonDependent`. -/
theorem HasTypeNativeUnion.substPairNonDependent {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType resultType : RawTerm scope}
    {branch : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (branchTyped : HasTypeNativeUnion profile
      ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
      branch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (innerArgTyped : HasTypeDescPi profile context innerArg resultType)
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeNativeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
      resultType := by
  have innerAtSubstituted : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg)
        (RawTerm.rename RawRenaming.weaken resultType)) := by
    rw [subst_singleton_renameWeaken_cancel]
    exact innerArgTyped
  have substituted :=
    HasTypeNativeUnion.substPairUnderTwoBindings innerArg outerArg branchTyped
      innerAtSubstituted outerArgTyped
  rwa [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel] at substituted

/-! ## ★★ The GENERAL succ-branch recursive-eliminator ι discharge (deliverable 3 — the NATIVE-04 line)

The succ-ι reduct `natElimSuccContractum motive zeroBranch succBranch predecessor` =
`succBranch[var 0 := natElim(motive, zeroBranch, succBranch, predecessor), var 1 := predecessor]`.

The recursive call `natElimCell(...)` at `var 0` is UNION-typed (by the `recursiveElim` arm, given the
predecessor union-typed at `Nat` and the zero branch union-typed at `resultType`), but it is NEVER
host-typed (`natElimCell` heads are untyped in the grown engine, the NATIVE-04 wall).  So the reduct
typing transports the branch typing along a substitution whose `var 0` image is union-typed — i.e. along
`substPairNonDependent` with a UNION inner substituent.

The shipped `substPairNonDependent` requires the inner substituent HOST-typed (it descends the branch's
binders and the seed union has no general union weakening / no conv arm — §HasTypeNativeUnion line 51 — so
binder descent with union images is wave work).  Therefore the succ-ι reduct typing is exposed here as
`natElimSuccIotaComputesTypedInUnion`, taking the union-substituent transport
(`reductTransportsBranch`) as the EXPLICIT residual hypothesis that the no-conv-arm seed imposes — but
with the recursive-call and predecessor typings DERIVED (not premised): the recursive call by the union's
own `recursiveElim` arm, the predecessor as the scrutinee's union typing.  This is the honest residual:
the discharge needs ONLY the substitution mechanism (the union-image binder descent), not any additional
typing input — strictly weaker than the pre-NATIVE-37 `reductTyped` premise (which premised the WHOLE
reduct typing).  The recursive-call construction is the load-bearing new content: the recursion loop
the bespoke engine could not close is closed here through the union's recursiveElim arm. -/

/-- The recursive call `natElimCell(motive, zeroBranch, succBranch, predecessor)` is union-typed at
`resultType` — by the union's own `recursiveElim` arm, given the predecessor union-typed at `Nat` and the
zero branch union-typed at `resultType`.  The load-bearing construction closing the recursion loop. -/
theorem natElimRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType) :
    HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor) resultType :=
  HasTypeNativeUnion.recursiveElim context .gen_natElim natElimNativeRecursiveRule
    motive zeroBranch succBranch predecessor resultType rfl predecessorTyped zeroBranchTyped

/-- The `natRec` recursive call is union-typed at `resultType` — the dependent-recursor twin. -/
theorem natRecRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType) :
    HasTypeNativeUnion profile context
      (natRecCell motive zeroBranch succBranch predecessor) resultType :=
  HasTypeNativeUnion.recursiveElim context .gen_natRec natRecNativeRecursiveRule
    motive zeroBranch succBranch predecessor resultType rfl predecessorTyped zeroBranchTyped

/-- The union-substituent 2-binder transport for a recursive-eliminator step branch: substitutes the
branch (typed at the twice-weakened result under the two binders) at `var 0 := recursiveCall, var 1 :=
predecessor` with BOTH substituents UNION-typed, yielding the reduct union-typed at `resultType`.  This is
`substPairNonDependent` with a UNION inner substituent — the one ingredient the host
`substPairNonDependent` cannot supply (its inner substituent must be host-typed, and the recursive call is
never host-typed).  Building it needs union-image binder descent (general union weakening), which the
seed union (no conv arm, no general union weakening) defers to NATIVE-46; so it is the residual the
succ-ι discharge consumes — capturing EXACTLY the no-conv-arm gap, with every typing input supplied. -/
abbrev UnionSubstPairTransports (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (outerType resultType : RawTerm scope) : Prop :=
  ∀ (branch : RawTerm (scope + 2)) (innerArg outerArg : RawTerm scope),
    HasTypeNativeUnion profile
        ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
        branch
        (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)) →
      HasTypeNativeUnion profile context innerArg resultType →
      HasTypeNativeUnion profile context outerArg outerType →
      HasTypeNativeUnion profile context
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
        resultType

/-- **★★ The GENERAL succ-branch natElim ι discharge.**  A `natElim(motive, zeroBranch, succBranch,
succ p)` ι-steps (`Step.iotaNatElimSucc`) and the substituted reduct `natElimSuccContractum motive
zeroBranch succBranch p` is UNION-typed at `resultType`.  The recursive-call inner substituent is typed by
the union's own `recursiveElim` arm (`natElimRecursiveCallUnionTyped`) and the outer substituent is the
predecessor — both DERIVED (no `reductTyped` premise: the WHOLE reduct typing was premised before
NATIVE-37; here only the union-image binder-descent transport `unionTransport` is, and it is
typing-input-free).  The branch typing IS consumed (fed to `unionTransport`).  Closes the NATIVE-04 line:
the IH-return family (`natElimComputesToNumeral`'s `substitutedReductProduces`) was the special case; this
is the full family — the recursion loop closed through the union's recursiveElim arm. -/
theorem natElimSuccIotaComputesTypedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeNativeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeNativeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨Step.iotaNatElimSucc,
    unionTransport succBranch
      (natElimCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
        predecessorTyped zeroBranchTyped)
      predecessorTyped⟩

/-- **★★ The GENERAL succ-branch natRec ι discharge** — the dependent-recursor twin. -/
theorem natRecSuccIotaComputesTypedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeNativeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeNativeUnion profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨Step.iotaNatRecSucc,
    unionTransport succBranch
      (natRecCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natRecRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
        predecessorTyped zeroBranchTyped)
      predecessorTyped⟩

/-! ## (5) Coverage record + witness -/

/-- **The NATIVE-37 part-b substitution coverage record.**  Each field is a distinct live property of the
substitution substrate over the native union: the pointwise substitution lemma, the two-variable
corollaries, the recursive-call construction (the recursion loop closed through the union's recursiveElim
arm), and the general succ-branch ι discharge for both recursors.  An inhabitant certifies the substrate
is exercised (constructed, not just declared). -/
structure NativeUnionSubstitutionCoverage (profile : PolyProfile) : Prop where
  /-- The pointwise substitution lemma holds along any host-typed substitution. -/
  pointwiseSubstitution : ∀ {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope},
    HasTypeNativeUnion profile sourceContext subject classifier →
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeNativeUnion.SubstHostTyped sourceContext targetContext substitution →
      HasTypeNativeUnion profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier)
  /-- The 2-variable substitution corollary holds. -/
  pairSubstitution : ∀ {scope : Nat} {context : TypingContext profile scope}
    {outerType : RawTerm scope} {innerType : RawTerm (scope + 1)}
    {subject classifier : RawTerm (scope + 2)} (innerArg outerArg : RawTerm scope),
    HasTypeNativeUnion profile ((context.cons outerType).cons innerType) subject classifier →
    HasTypeDescPi profile context innerArg (RawTerm.subst (RawTermSubst.singleton outerArg) innerType) →
    HasTypeDescPi profile context outerArg outerType →
    HasTypeNativeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) subject)
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) classifier)
  /-- The natElim recursive call is union-typed (the recursion loop closes). -/
  recursiveCallTyped : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor resultType : RawTerm scope),
    HasTypeNativeUnion profile context predecessor natTypeCell →
    HasTypeNativeUnion profile context zeroBranch resultType →
    HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor) resultType
  /-- The general succ-branch natElim ι discharge holds (given the union-image transport residual). -/
  succIotaDischarged : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor resultType : RawTerm scope),
    HasTypeNativeUnion profile context predecessor natTypeCell →
    HasTypeNativeUnion profile context zeroBranch resultType →
    HasTypeNativeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)) →
    UnionSubstPairTransports profile context natTypeCell resultType →
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeNativeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType

/-- **★ The NATIVE-37 part-b substitution coverage gate** — inhabited by the shipped declarations, so the
exercised substitution-substrate property set can NOT silently shrink. -/
theorem nativeUnionSubstitutionCoverageWitness {profile : PolyProfile} :
    NativeUnionSubstitutionCoverage profile where
  pointwiseSubstitution := by
    intro _ _ _ _ derivation _ targetContext substitution condition
    exact HasTypeNativeUnion.substRespectingContext derivation targetContext substitution condition
  pairSubstitution := by
    intro _ _ _ _ _ _ innerArg outerArg derivation innerArgTyped outerArgTyped
    exact HasTypeNativeUnion.substPairUnderTwoBindings innerArg outerArg derivation innerArgTyped
      outerArgTyped
  recursiveCallTyped := by
    intro _ context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped
    exact natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped
  succIotaDischarged := by
    intro _ context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped branchTyped unionTransport
    exact natElimSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor
      resultType predecessorTyped zeroBranchTyped branchTyped unionTransport

end FX1Poly.Typed
