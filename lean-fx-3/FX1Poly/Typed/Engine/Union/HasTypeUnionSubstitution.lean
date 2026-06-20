import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Ledger.Cell.UnionCellSubstitution
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiSubstPair
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubstLift
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Typed/HasTypeUnionSubstitution — NATIVE-37 part b: the SUBSTITUTION lemma for the
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

  * the SOLE ENGINE EMBEDDING (`ofGrown`) and the nine scrutinee/host-premise arms route their host
    premises through the grown engine's own `substRespectingContext` (host substituents are exactly what
    it demands) and re-embed; the TABLE-DRIVEN FORMATION arms (`formationRule` / `dataIntroNullary`)
    substitute their premise telescope via the flat / term-indexed
    telescope `substRespectingContext` helpers and reconstruct via `RawTerm.subst_mkGen_of_ne_var` (the
    base-type/data-intro/flat/term-indexed-former standalone engines were retired into table arms,
    TABLE-CANON-6);
  * the seven RECURSIVE native arms (`gradedBinderIntro` / `generalElim` / `recursiveElim` /
    `twoBranchMatchElim` / `pathInductionElim` / `projectionElim` / `recursiveUnaryIntro` /
    `recursiveBinaryIntro`) recurse via the induction hypotheses, with `RawTermSubst.lift` crossing the
    one/two binders (the lifted condition keeps the images host-typed: `0` → the fresh `var` via
    `ofFormation`, `k+1` → the host image weakened).

The graded arm additionally transports the affine binder check
(`RawTerm.occurrenceCountAt_subst_lift_zeroPosition`: a lifted substitution preserves the freshest-binder
occurrence count, so `gradedBinderChecks usage body` survives verbatim).

## ★ The 2-variable corollaries + the succ-ι discharge

  * `HasTypeUnion.substPairUnderTwoBindings` / `substPairNonDependent` — the union mirrors of the
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
audit-gated in `FX1PolyAudit/AuditUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-- The host-substituent context condition for the native union: every variable image is HOST-typed at
the substituted lookup type. -/
abbrev HasTypeUnion.SubstHostTyped {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    HasTypeDescPi profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index))

/-- A host-typed image is a union image (via `ofGrown`) — the bridge each recursive arm's IH uses to feed
its native premises a union substituent built from the host condition. -/
theorem HasTypeUnion.SubstHostTyped.toUnionImage {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeUnion.SubstHostTyped sourceContext targetContext substitution)
    (index : Fin sourceScope) :
    HasTypeUnion profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index)) :=
  HasTypeUnion.ofGrown (condition index)

/-- The two-binder lift of the host-substituent condition (the recursiveElim / idJ succ-branch shape):
the double lift of a host condition is a host condition at the context extended by the two domains.  An
iterate of `substContextCondition_cons`. -/
theorem HasTypeUnion.SubstHostTyped.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeUnion.SubstHostTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstHostTyped ((sourceContext.cons outerType).cons innerType)
      ((targetContext.cons (RawTerm.subst substitution outerType)).cons
        (RawTerm.subst (iterateLiftRaw substitution 1) innerType))
      (iterateLiftRaw substitution 2) := by
  have outerStep :
      HasTypeUnion.SubstHostTyped (sourceContext.cons outerType)
        (targetContext.cons (RawTerm.subst substitution outerType))
        (iterateLiftRaw substitution 1) :=
    substContextCondition_cons outerType substitution condition
  have innerStep :
      HasTypeUnion.SubstHostTyped ((sourceContext.cons outerType).cons innerType)
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
theorem HasTypeUnion.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstHostTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext substitution condition
      have typedSubst := typedIH targetContext substitution condition
      have reclassifierSubst := reclassifierIH targetContext substitution condition
      rw [subst_universeCodeCell] at reclassifierSubst
      exact HasTypeUnion.conv levelExpr flag typedSubst
        (Conv.subst substitution converts) reclassifierSubst
  | ofGrown hostTyped =>
      intro targetScope targetContext substitution condition
      exact HasTypeUnion.ofGrown
        (hostTyped.substRespectingContext targetContext substitution condition)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      intro targetScope targetContext substitution condition
      cases rule with
      | baseType baseRule =>
          have isBaseType : baseTypeRuleDescOf generator = some baseRule :=
            formationRuleOf_baseType_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var := baseTypeRuleImpliesNotVariable isBaseType
          dsimp only [FormationRule.outputType]
          rw [RawTerm.subst_mkGen_of_ne_var substitution hNotVar,
            baseTypeRuleDescOf_outputSubstStable isBaseType substitution]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children) (.baseType baseRule)
            levels (RawTerm.subst substitution carrier) level flag isFormationRule trivial
      | flat flatRule =>
          have isFlatFormation : flatTypingRuleDescOf generator = some flatRule :=
            formationRuleOf_flat_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            flatFormationRuleImpliesNotVariable isFlatFormation
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            flatFormationRuleIsUniverseFormer isFlatFormation
          have flatPremise : FlatDescTelescopePi profile context flag levels children := premise
          have substPremise :=
            FlatDescTelescopePi.substRespectingTelescope flatPremise targetContext substitution
              (fun index => condition index)
          dsimp only [FormationRule.outputType, universeFormerOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.flat { outputType := universeFormerOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule substPremise
      | termIndexed termRule =>
          have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
            formationRuleOf_termIndexed_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            termIndexedFormerRuleImpliesNotVariable isTermIndexed
          obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
            termIndexedFormerRuleIsCarrierOutput isTermIndexed
          have termPremise : TermIndexedFormerTelescope profile context children carrier level flag :=
            premise
          have substPremises :=
            TermIndexedFormerTelescope.substRespectingContext termPremise targetContext substitution
              condition
          dsimp only [FormationRule.outputType, termIndexedCarrierOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.termIndexed { outputType := termIndexedCarrierOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule substPremises
  | dataIntroNullary context generator payload children rule isDataIntro =>
      intro targetScope targetContext substitution _condition
      have hNotVar : generator ≠ Generator.gen_var := dataIntroNullaryRuleImpliesNotVariable isDataIntro
      rw [RawTerm.subst_mkGen_of_ne_var substitution hNotVar,
        dataIntroNullaryRuleDescOf_outputSubstStable isDataIntro substitution]
      exact HasTypeUnion.dataIntroNullary targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) rule isDataIntro
  | recursiveDataIntro context generator spec head recursiveChild elementType isRecursiveDataIntro
      headTyped _recursiveChildTyped recursiveChildIH =>
      intro targetScope targetContext substitution condition
      rcases recursiveDataIntroSpecOf_cases
          (show recursiveDataIntroSpecOf generator = some spec from isRecursiveDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩
      · subst specEq
        have childSubst := recursiveChildIH targetContext substitution condition
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (natSuccCell recursiveChild))
          (RawTerm.subst substitution natTypeCell)
        rw [subst_natSuccCell, subst_natTypeCell]
        exact HasTypeUnion.recursiveUnaryIntro targetContext .gen_natSucc
          natSuccNativeRecursiveUnaryRule (RawTerm.subst substitution recursiveChild) rfl childSubst
      · subst specEq
        have tailSubst := recursiveChildIH targetContext substitution condition
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (listConsCell head recursiveChild))
          (RawTerm.subst substitution (listTypeCell elementType))
        rw [subst_listConsCell, subst_listTypeCell]
        exact HasTypeUnion.recursiveBinaryIntro targetContext .gen_listCons
          listConsNativeRecursiveBinaryRule (RawTerm.subst substitution head)
          (RawTerm.subst substitution recursiveChild) (RawTerm.subst substitution elementType) rfl
          ((headTyped rfl).substRespectingContext targetContext substitution condition) tailSubst
  | grownDataIntro context generator spec child0 child1 typeParam0 typeParam1 formednessLevel
      formednessFlag isGrownDataIntro child0Typed child1Typed formednessTyped =>
      intro targetScope targetContext substitution condition
      rcases grownDataIntroSpecOf_cases
          (show grownDataIntroSpecOf generator = some spec from isGrownDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩
          | ⟨_, specEq⟩
      · subst specEq
        -- optionSome row: one grown child at the element type, output optionTypeCell.
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (optionSomeCell child0))
          (RawTerm.subst substitution (optionTypeCell typeParam0))
        rw [subst_optionSomeCell, subst_optionTypeCell]
        exact HasTypeUnion.pinnedUnaryIntro targetContext .gen_optionSome
          optionSomeNativePinnedUnaryRule (RawTerm.subst substitution child0)
          (RawTerm.subst substitution typeParam0) rfl
          ((child0Typed rfl).substRespectingContext targetContext substitution condition)
      · subst specEq
        -- optionNone row: childless, grown-formedness on the free element type.
        have elementFormSubst :=
          (formednessTyped rfl).substRespectingContext targetContext substitution condition
        rw [subst_universeCodeCell] at elementFormSubst
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution optionNoneCell)
          (RawTerm.subst substitution (optionTypeCell typeParam0))
        rw [subst_optionNoneCell, subst_optionTypeCell]
        exact HasTypeUnion.nullaryFreeTypeIntro targetContext .gen_optionNone
          optionNoneNativeNullaryFreeTypeRule (RawTerm.subst substitution typeParam0)
          formednessLevel formednessFlag rfl elementFormSubst
      · subst specEq
        -- listNil row: the optionNone twin with the list container.
        have elementFormSubst :=
          (formednessTyped rfl).substRespectingContext targetContext substitution condition
        rw [subst_universeCodeCell] at elementFormSubst
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution listNilCell)
          (RawTerm.subst substitution (listTypeCell typeParam0))
        rw [subst_listNilCell, subst_listTypeCell]
        exact HasTypeUnion.nullaryFreeTypeIntro targetContext .gen_listNil
          listNilNativeNullaryFreeTypeRule (RawTerm.subst substitution typeParam0)
          formednessLevel formednessFlag rfl elementFormSubst
      · subst specEq
        -- eitherInl row: grown value at the pinned left, formedness on the free right.
        have valueSubst :=
          (child0Typed rfl).substRespectingContext targetContext substitution condition
        have freeFormSubst :=
          (formednessTyped rfl).substRespectingContext targetContext substitution condition
        rw [subst_universeCodeCell] at freeFormSubst
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (eitherInlCell child0))
          (RawTerm.subst substitution (eitherTypeCell typeParam0 typeParam1))
        rw [subst_eitherInlCell, subst_eitherTypeCell]
        exact HasTypeUnion.coproductIntro targetContext .gen_eitherInl
          eitherInlNativeCoproductRule (RawTerm.subst substitution child0)
          (RawTerm.subst substitution typeParam0) (RawTerm.subst substitution typeParam1)
          formednessLevel formednessFlag rfl valueSubst freeFormSubst
      · subst specEq
        -- eitherInr row: grown value pinning the right, free left first in the output.
        have valueSubst :=
          (child0Typed rfl).substRespectingContext targetContext substitution condition
        have freeFormSubst :=
          (formednessTyped rfl).substRespectingContext targetContext substitution condition
        rw [subst_universeCodeCell] at freeFormSubst
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (eitherInrCell child0))
          (RawTerm.subst substitution (eitherTypeCell typeParam1 typeParam0))
        rw [subst_eitherInrCell, subst_eitherTypeCell]
        exact HasTypeUnion.coproductIntro targetContext .gen_eitherInr
          eitherInrNativeCoproductRule (RawTerm.subst substitution child0)
          (RawTerm.subst substitution typeParam0) (RawTerm.subst substitution typeParam1)
          formednessLevel formednessFlag rfl valueSubst freeFormSubst
      · subst specEq
        -- pair row: two grown children at two independent type params.
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (pairCell child0 child1))
          (RawTerm.subst substitution (productTypeCell typeParam0 typeParam1))
        rw [subst_pairCell, subst_productTypeCell]
        exact HasTypeUnion.nonDependentBinaryIntro targetContext .gen_pair
          pairNativeNonDependentBinaryRule (RawTerm.subst substitution child0)
          (RawTerm.subst substitution child1) (RawTerm.subst substitution typeParam0)
          (RawTerm.subst substitution typeParam1) rfl
          ((child0Typed rfl).substRespectingContext targetContext substitution condition)
          ((child1Typed rfl).substRespectingContext targetContext substitution condition)
      · subst specEq
        -- refl row: grown witness, term-indexed Id(typeParam0, child0, child0) output.
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (reflCell child0))
          (RawTerm.subst substitution (idTypeCell typeParam0 child0 child0))
        rw [subst_reflCell, subst_idTypeCell]
        exact HasTypeUnion.reflexiveIntro targetContext .gen_refl
          reflNativeReflexiveRule (RawTerm.subst substitution child0)
          (RawTerm.subst substitution typeParam0) rfl
          ((child0Typed rfl).substRespectingContext targetContext substitution condition)
  | elim context generator rule args params isElim premisesHold ihPremises =>
      intro targetScope targetContext substitution condition
      -- The unified eliminator arm: pin the row, destructure the children + type indices, source each
      -- premise's substituted typing from `ihPremises` at the obligation's list membership, then rebuild
      -- through the pre-collapse smart constructor (which threads the `elim` arm at the matching row).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app row
      · match args, params with
        | .childCons eliminated (.childCons argument .childNil),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have eliminatedSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have argumentSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_piTyCodeCell] at eliminatedSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (appCell eliminated argument))
            (RawTerm.subst substitution (RawTerm.subst0 typeParamB argument))
          rw [subst_appCell, RawTerm.subst0_subst_commute]
          exact HasTypeUnion.generalElim targetContext .gen_app appGeneralElimRule
            (RawTerm.subst substitution typeParamA)
            (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB)
            (RawTerm.subst substitution typeParamA) (RawTerm.subst substitution typeParamA)
            (RawTerm.subst substitution eliminated) (RawTerm.subst substitution argument)
            rfl eliminatedSubst argumentSubst
      -- pathApp row
      · match args, params with
        | .childCons eliminated (.childCons argument .childNil),
          .childCons typeParamA (.childCons typeParamC (.childCons typeParamD .childNil)) =>
          have eliminatedSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have argumentSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_bridgeTypeCell] at eliminatedSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pathAppCell eliminated argument))
            (RawTerm.subst substitution typeParamA)
          rw [subst_pathAppCell]
          exact HasTypeUnion.generalElim targetContext .gen_pathApp pathAppGeneralElimRule
            (RawTerm.subst substitution typeParamA)
            (RawTerm.weaken (RawTerm.subst substitution typeParamA))
            (RawTerm.subst substitution typeParamC) (RawTerm.subst substitution typeParamD)
            (RawTerm.subst substitution eliminated) (RawTerm.subst substitution argument)
            rfl eliminatedSubst argumentSubst
      -- natElim row
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepLiftedCondition :=
            HasTypeUnion.SubstHostTyped.consTwice natTypeCell
              (RawTerm.weaken resultType) condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2) stepLiftedCondition
          rw [subst_natTypeCell] at scrutineeSubst
          dsimp only [RawTerm.weaken] at stepBranchSubst
          rw [subst_iterateLift_one_renameWeaken_commute,
            subst_iterateLift_two_weaken_weaken_commute] at stepBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_natElimCell]
          exact HasTypeUnion.recursiveElim targetContext .gen_natElim
            natElimNativeRecursiveRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
            (RawTerm.subst substitution baseBranch)
            (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
            (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution resultType)
            rfl scrutineeSubst baseBranchSubst stepBranchSubst
      -- natRec row
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepLiftedCondition :=
            HasTypeUnion.SubstHostTyped.consTwice natTypeCell
              (RawTerm.weaken resultType) condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2) stepLiftedCondition
          rw [subst_natTypeCell] at scrutineeSubst
          dsimp only [RawTerm.weaken] at stepBranchSubst
          rw [subst_iterateLift_one_renameWeaken_commute,
            subst_iterateLift_two_weaken_weaken_commute] at stepBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_natRecCell]
          exact HasTypeUnion.recursiveElim targetContext .gen_natRec
            natRecNativeRecursiveRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
            (RawTerm.subst substitution baseBranch)
            (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
            (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution resultType)
            rfl scrutineeSubst baseBranchSubst stepBranchSubst
      -- boolElim row
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons firstBranch (.childCons secondBranch .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (boolElimCell motive scrutinee firstBranch secondBranch))
            (RawTerm.subst substitution resultType)
          rw [subst_boolElimCell]
          exact HasTypeUnion.twoBranchMatchElim targetContext .gen_boolElim
            boolElimNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
            (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
            (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
            (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
            rfl scrutineeSubst firstBranchSubst secondBranchSubst
      -- optionMatch row
      · match args, params with
        | .childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_optionTypeCell] at scrutineeSubst
          rw [subst_nonDependentArrow] at secondBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionMatchCell motive firstBranch secondBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_optionMatchCell]
          exact HasTypeUnion.twoBranchMatchElim targetContext .gen_optionMatch
            optionMatchNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
            (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
            (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
            (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
            rfl scrutineeSubst firstBranchSubst secondBranchSubst
      -- eitherMatch row
      · match args, params with
        | .childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_eitherTypeCell] at scrutineeSubst
          rw [subst_nonDependentArrow] at firstBranchSubst
          rw [subst_nonDependentArrow] at secondBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherMatchCell motive firstBranch secondBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_eitherMatchCell]
          exact HasTypeUnion.twoBranchMatchElim targetContext .gen_eitherMatch
            eitherMatchNativeMatchRule (RawTerm.subst (iterateLiftRaw substitution 1) motive)
            (RawTerm.subst substitution firstBranch) (RawTerm.subst substitution secondBranch)
            (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution typeParamA)
            (RawTerm.subst substitution typeParamB) (RawTerm.subst substitution resultType)
            rfl scrutineeSubst firstBranchSubst secondBranchSubst
      -- idJ row
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons endpoint (.childCons resultType .childNil)) =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseCaseSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_idTypeCell] at witnessSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (idJCell motive baseCase witness))
            (RawTerm.subst substitution resultType)
          rw [subst_idJCell]
          exact HasTypeUnion.pathInductionElim targetContext .gen_idJ idJNativePathInductionRule
            (RawTerm.subst (iterateLiftRaw substitution 2) motive)
            (RawTerm.subst substitution baseCase) (RawTerm.subst substitution witness)
            (RawTerm.subst substitution typeCode) (RawTerm.subst substitution endpoint)
            (RawTerm.subst substitution resultType) rfl witnessSubst baseCaseSubst
      -- fst row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (fstCell pairTerm)) (RawTerm.subst substitution firstType)
          rw [subst_fstCell]
          exact HasTypeUnion.projectionElim targetContext .gen_fst fstNativeProjectionRule
            (RawTerm.subst substitution pairTerm) (RawTerm.subst substitution firstType)
            (RawTerm.subst substitution secondType) rfl pairSubst
      -- snd row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (sndCell pairTerm)) (RawTerm.subst substitution secondType)
          rw [subst_sndCell]
          exact HasTypeUnion.projectionElim targetContext .gen_snd sndNativeProjectionRule
            (RawTerm.subst substitution pairTerm) (RawTerm.subst substitution firstType)
            (RawTerm.subst substitution secondType) rfl pairSubst
      -- listElim row
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons resultType .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have nilSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have consSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_listTypeCell] at scrutineeSubst
          rw [subst_listStepFunctionType] at consSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.subst substitution resultType)
          rw [subst_listElimCell]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution nilBranch)
                  (.childCons (RawTerm.subst substitution consBranch) .childNil))))
            (.childCons (RawTerm.subst substitution elementType)
              (.childCons (RawTerm.subst substitution resultType) .childNil)) rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact nilSubst
            | tail _ hmem => cases hmem with
              | head => exact consSubst
              | tail _ hmem => cases hmem
  | gradedBinderIntro context generator rule typeParamA typeParamB body domainLevel codomainLevel flag
      isIntro binderGraded _domainFormed _classifierFormed _bodyTyped domainIH classifierIH bodyIH =>
      intro targetScope targetContext substitution condition
      -- The lifted host condition for the body / classifier IHs (the binder-crossing leg).
      have liftedCondition :
          HasTypeUnion.SubstHostTyped
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
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (lamCell typeParamA body))
          (RawTerm.subst substitution (piTyCodeCell typeParamA typeParamB))
        rw [subst_lamCell, subst_piTyCodeCell]
        exact HasTypeUnion.gradedBinderIntro targetContext .gen_lam lamGradedIntroRule
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
        show HasTypeUnion profile targetContext
          (RawTerm.subst substitution (pathLamCell body))
          (RawTerm.subst substitution
            (bridgeTypeCell typeParamA (RawTerm.subst0 body intervalZeroCell)
              (RawTerm.subst0 body intervalOneCell)))
        rw [subst_pathLamCell, subst_bridgeTypeCell, RawTerm.subst0_subst_commute,
          RawTerm.subst0_subst_commute]
        exact HasTypeUnion.gradedBinderIntro targetContext .gen_pathLam pathLamGradedIntroRule
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
`HasTypeUnion`, with subject and classifier substituted.  The inner substituent is host-typed at the
OUTER-SUBSTITUTED inner binder type.  The union mirror of `HasTypeDescPi.substPairUnderTwoBindings`,
instantiating `substRespectingContext` at `cons innerArg (singleton outerArg)` — the `Fin` 0 / 1 / k+2
split is verbatim the host proof's. -/
theorem HasTypeUnion.substPairUnderTwoBindings {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType : RawTerm scope}
    {innerType : RawTerm (scope + 1)} {subject classifier : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (derivation :
      HasTypeUnion profile ((context.cons outerType).cons innerType) subject classifier)
    (innerArgTyped : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg) innerType))
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeUnion profile context
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
theorem HasTypeUnion.substPairNonDependent {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType resultType : RawTerm scope}
    {branch : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (branchTyped : HasTypeUnion profile
      ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
      branch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (innerArgTyped : HasTypeDescPi profile context innerArg resultType)
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
      resultType := by
  have innerAtSubstituted : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg)
        (RawTerm.rename RawRenaming.weaken resultType)) := by
    rw [subst_singleton_renameWeaken_cancel]
    exact innerArgTyped
  have substituted :=
    HasTypeUnion.substPairUnderTwoBindings innerArg outerArg branchTyped
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
binders and the seed union has no general union weakening / no conv arm — §HasTypeUnion line 51 — so
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
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (stepBranchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))) :
    HasTypeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor) resultType :=
  HasTypeUnion.recursiveElim context .gen_natElim natElimNativeRecursiveRule
    motive zeroBranch succBranch predecessor resultType rfl predecessorTyped zeroBranchTyped
    stepBranchTyped

/-- The `natRec` recursive call is union-typed at `resultType` — the dependent-recursor twin. -/
theorem natRecRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (stepBranchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken resultType))) :
    HasTypeUnion profile context
      (natRecCell motive zeroBranch succBranch predecessor) resultType :=
  HasTypeUnion.recursiveElim context .gen_natRec natRecNativeRecursiveRule
    motive zeroBranch succBranch predecessor resultType rfl predecessorTyped zeroBranchTyped
    stepBranchTyped

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
    HasTypeUnion profile
        ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
        branch
        (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)) →
      HasTypeUnion profile context innerArg resultType →
      HasTypeUnion profile context outerArg outerType →
      HasTypeUnion profile context
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
        resultType

/-- **★★ The GENERAL succ-branch natElim ι discharge.**  A `natElim(motive, zeroBranch, succBranch,
succ p)` ι-steps (`IotaHeadStep.iotaNatElimSucc.toStep`) and the substituted reduct `natElimSuccContractum motive
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
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨IotaHeadStep.iotaNatElimSucc.toStep,
    unionTransport succBranch
      (natElimCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
        predecessorTyped zeroBranchTyped branchTyped)
      predecessorTyped⟩

/-- **★★ The GENERAL succ-branch natRec ι discharge** — the dependent-recursor twin. -/
theorem natRecSuccIotaComputesTypedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor resultType : RawTerm scope)
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨IotaHeadStep.iotaNatRecSucc.toStep,
    unionTransport succBranch
      (natRecCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natRecRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
        predecessorTyped zeroBranchTyped branchTyped)
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
    HasTypeUnion profile sourceContext subject classifier →
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstHostTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier)
  /-- The 2-variable substitution corollary holds. -/
  pairSubstitution : ∀ {scope : Nat} {context : TypingContext profile scope}
    {outerType : RawTerm scope} {innerType : RawTerm (scope + 1)}
    {subject classifier : RawTerm (scope + 2)} (innerArg outerArg : RawTerm scope),
    HasTypeUnion profile ((context.cons outerType).cons innerType) subject classifier →
    HasTypeDescPi profile context innerArg (RawTerm.subst (RawTermSubst.singleton outerArg) innerType) →
    HasTypeDescPi profile context outerArg outerType →
    HasTypeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) subject)
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) classifier)
  /-- The natElim recursive call is union-typed (the recursion loop closes), given the step branch's
  union typing at the two-binder step shape. -/
  recursiveCallTyped : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor resultType : RawTerm scope),
    HasTypeUnion profile context predecessor natTypeCell →
    HasTypeUnion profile context zeroBranch resultType →
    HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)) →
    HasTypeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor) resultType
  /-- The general succ-branch natElim ι discharge holds (given the union-image transport residual). -/
  succIotaDischarged : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor resultType : RawTerm scope),
    HasTypeUnion profile context predecessor natTypeCell →
    HasTypeUnion profile context zeroBranch resultType →
    HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)) →
    UnionSubstPairTransports profile context natTypeCell resultType →
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType

/-- **★ The NATIVE-37 part-b substitution coverage gate** — inhabited by the shipped declarations, so the
exercised substitution-substrate property set can NOT silently shrink. -/
theorem nativeUnionSubstitutionCoverageWitness {profile : PolyProfile} :
    NativeUnionSubstitutionCoverage profile where
  pointwiseSubstitution := by
    intro _ _ _ _ derivation _ targetContext substitution condition
    exact HasTypeUnion.substRespectingContext derivation targetContext substitution condition
  pairSubstitution := by
    intro _ _ _ _ _ _ innerArg outerArg derivation innerArgTyped outerArgTyped
    exact HasTypeUnion.substPairUnderTwoBindings innerArg outerArg derivation innerArgTyped
      outerArgTyped
  recursiveCallTyped := by
    intro _ context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped stepBranchTyped
    exact natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped stepBranchTyped
  succIotaDischarged := by
    intro _ context motive zeroBranch succBranch predecessor resultType
      predecessorTyped zeroBranchTyped branchTyped unionTransport
    exact natElimSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor
      resultType predecessorTyped zeroBranchTyped branchTyped unionTransport

end FX1Poly.Typed
