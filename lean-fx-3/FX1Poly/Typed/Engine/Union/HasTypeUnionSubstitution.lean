import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Cell.UnionCellSubstitution
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiSubstPair
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubstLift
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Typed/HasTypeUnionSubstitution — NATIVE-37 part b: the SUBSTITUTION lemma for the
    5-arm native union + the 2-variable corollaries + the GENERAL succ-branch recursive-eliminator ι

This file discharges the campaign's longest-standing residual (the NATIVE-04 line): typing the succ-ι
reduct `succBranch[var 0 := natElim(...), var 1 := predecessor]` for an ARBITRARY typed branch.  Since
NATIVE-04 the host 2-variable substitution lemma (`HasTypeDescPi.substPairUnderTwoBindings`) existed but
its premises are HOST typings — and the recursive call `natElimCell(...)` is never host-typed.  The
union now contains everything; this file restates substitution over it.

## The substituent discipline (HOST-typed images — the universally-closeable formulation)

`substRespectingContext` is preserved along any substitution whose variable images are HOST-typed
(`HasTypeDescPi`) at the substituted lookup types.  Every host image is also a union image (via
`ofGrown`), so the side condition is the strongest one that lets EVERY arm close:

  * the SOLE ENGINE EMBEDDING (`ofGrown`) routes its host premise through the grown engine's own
    `substRespectingContext` (host substituents are exactly what it demands) and re-embeds; the unified
    TABLE-DRIVEN FORMATION arm (`formationRule`) substitutes its premise telescope via the flat / term-indexed
    telescope `substRespectingContext` helpers and reconstructs via `RawTerm.subst_mkGen_of_ne_var` (the
    base-type/data-intro/flat/term-indexed-former standalone engines were retired into table arms,
    TABLE-CANON-6);
  * the unified RECURSIVE native arms `intro` and `elim` (each reading one rule row, with the introducer
    families folded into `intro` and the eliminator families into `elim`) recurse via the induction
    hypotheses over their rule obligation lists, with `RawTermSubst.lift` crossing the one/two binders (the
    lifted condition keeps the images host-typed: `0` → the fresh `var` via `ofFormation`, `k+1` → the host
    image weakened); the `conv` arm recurses on both the typed and the reclassifier premise.

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

`substRespectingContext` is `induction` over the 5 arms + the cell-subst `rfl` commutations + the
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
substituted classifier.  By `induction` over the 5 arms: the `ofGrown` embedding and the `formationRule`
arm route through the engines' own `substRespectingContext` (host substituents are exactly what they
demand) and re-embed; the recursive `intro` / `elim` arms recurse via the IHs over their rule obligations
with `RawTermSubst.lift` crossing binders, and the `conv` arm recurses on both premises; the `intro` arm
transports the affine binder check by the lifted-occurrence preservation. -/
theorem HasTypeUnion.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var context index =>
      intro targetScope targetContext substitution condition
      rw [subst_variableCell]
      exact condition index
  | universeFormation context levelExpr flag =>
      intro targetScope targetContext substitution condition
      rw [subst_universeCodeCell, subst_universeCodeCell]
      exact HasTypeUnion.universeFormation targetContext levelExpr flag
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext substitution condition
      have typedSubst := typedIH targetContext substitution condition
      have reclassifierSubst := reclassifierIH targetContext substitution condition
      rw [subst_universeCodeCell] at reclassifierSubst
      exact HasTypeUnion.conv levelExpr flag typedSubst
        (Conv.subst substitution converts) reclassifierSubst
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold ihPremises =>
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
          -- TYTAB-2 formationRule promotion: the premise is now the UNION obligation list, pushed through
          -- the substitution by `FormationRule.obligations_pushSubst` (each obligation sourced from
          -- `ihPremises`), and reconstructed by the union-obligation builder.  No grown telescope.
          have isFlatFormation : flatTypingRuleDescOf generator = some flatRule :=
            formationRuleOf_flat_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            flatFormationRuleImpliesNotVariable isFlatFormation
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            flatFormationRuleIsUniverseFormer isFlatFormation
          dsimp only [FormationRule.outputType, universeFormerOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.flat { outputType := universeFormerOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.flat { outputType := universeFormerOutput })
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
      | cumulative cumulativeRule =>
          -- TYTAB-2 wave U2: `formationRuleOf` now PRODUCES the four cumulative codes (Π / Σ / list /
          -- option) plus the nullary unit code.  ROW-SHAPE-AGNOSTIC (no concrete `cumulativeRule`): the
          -- non-`gen_var` witness comes from `formationRuleImpliesNotVariable`, the output is rewritten
          -- through the substitution by the row-shape-agnostic `typingRuleDescOf_output_substStable` (uniform
          -- over the universe-former Π/Σ/list/option rows AND the flag-pinned nullary unit row), and the
          -- premise is the UNION obligation list pushed through the substitution by
          -- `FormationRule.obligations_pushSubst` — its `crossingTypings` clause supplies the Π/Σ
          -- binder-crossing codomain from `ihPremises` at the lifted substitution.
          have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            cumulativeFormationRuleImpliesNotVariable isCumulative
          dsimp only [FormationRule.outputType]
          rw [typingRuleDescOf_output_substStable isCumulative substitution levels flag,
            RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.cumulative cumulativeRule)
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.cumulative cumulativeRule)
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
      | termIndexed termRule =>
          have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
            formationRuleOf_termIndexed_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            termIndexedFormerRuleImpliesNotVariable isTermIndexed
          obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
            termIndexedFormerRuleIsCarrierOutput isTermIndexed
          dsimp only [FormationRule.outputType, termIndexedCarrierOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.termIndexed { outputType := termIndexedCarrierOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.termIndexed { outputType := termIndexedCarrierOutput })
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
  | elim context generator rule args params level0 level1 flag isElim premisesHold ihPremises =>
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
          -- `app` is non-self-certifying (2 obligations): only function + argument premises.
          refine HasTypeUnion.elim targetContext .gen_app appElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact eliminatedSubst
          | tail _ hmem => cases hmem with
            | head => exact argumentSubst
            | tail _ hmem => cases hmem
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
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          rw [subst_pathAppCell]
          refine HasTypeUnion.elim targetContext .gen_pathApp pathAppElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamC)
                (.childCons (RawTerm.subst substitution typeParamD) .childNil)))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact eliminatedSubst
          | tail _ hmem => cases hmem with
            | head => exact argumentSubst
            | tail _ hmem => cases hmem with
              | head => exact resultSubst
              | tail _ hmem => cases hmem
      -- natElim row: DEPENDENT — output `subst0 motive scrutinee`; base branch at the motive at zero
      -- (`subst0_subst_commute`, the closed `natZeroCell` defeq-erases under any substitution), step branch
      -- under TWO binders (`natTypeCell`, then `motive`) at `natElimDependentSuccBranchType motive` (reshaped
      -- by the substitution-naturality corollary `subst_natElimDependentSuccBranchType_iterateLift`), motive
      -- obligation under one `natTypeCell` binder (its host condition via `substContextCondition_cons`).
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice natTypeCell motive condition)
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons natTypeCell substitution condition)
          rw [subst_natTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at baseBranchSubst
          rw [subst_natElimDependentSuccBranchType_iterateLift] at stepBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_natElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_natElim natElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- natRec row: DEPENDENT — verbatim twin of the `natElim` row (output `subst0 motive scrutinee`, base
      -- branch at zero, step branch under the two succ binders via the naturality corollary, motive under
      -- one `natTypeCell` binder); only the cell former (`natRecCell`) and generator (`gen_natRec`) differ.
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice natTypeCell motive condition)
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons natTypeCell substitution condition)
          rw [subst_natTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at baseBranchSubst
          rw [subst_natElimDependentSuccBranchType_iterateLift] at stepBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_natRecCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_natRec natRecElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- boolElim row: DEPENDENT — output `subst0 motive scrutinee`, branches at the motive at the boolean
      -- values (reshaped via `subst0_subst_commute`, the `app` template), motive obligation under one
      -- `boolTypeCell` binder (its host condition via `substContextCondition_cons`).
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons firstBranch (.childCons secondBranch .childNil))),
          .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons boolTypeCell substitution condition)
          rw [RawTerm.subst0_subst_commute] at firstBranchSubst secondBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (boolElimCell motive scrutinee firstBranch secondBranch))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_boolElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_boolElim boolElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution firstBranch)
                  (.childCons (RawTerm.subst substitution secondBranch) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact firstBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact secondBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- optionMatch row: DEPENDENT — output `subst0 motive scrutinee`; the none branch is nullary at
      -- `subst0 motive optionNoneCell` (reshaped via `subst0_subst_commute`, the bool/app template; the closed
      -- `optionNoneCell` defeq-erases under any substitution), the some branch at the dependent some branch type
      -- (reshaped by `subst_optionMatchDependentSomeBranchType_iterateLift`); motive obligation under one
      -- `optionTypeCell` binder (its host condition via `substContextCondition_cons`).
      · match args, params with
        | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have noneBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have someBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (optionTypeCell typeParamA) substitution condition)
          rw [subst_optionTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at noneBranchSubst
          rw [subst_optionMatchDependentSomeBranchType_iterateLift] at someBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionMatchCell motive noneBranch someBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_optionMatchCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_optionMatch optionMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution noneBranch)
                (.childCons (RawTerm.subst substitution someBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact noneBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact someBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- eitherMatch row: DEPENDENT — output `subst0 motive scrutinee`; branches at the dependent inl/inr
      -- branch types (reshaped by `subst_eitherMatchDependentInl/InrBranchType_iterateLift`); motive
      -- obligation under one `eitherTypeCell` binder (its host condition via `substContextCondition_cons`).
      · match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have leftBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have rightBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (eitherTypeCell typeParamA typeParamB) substitution condition)
          rw [subst_eitherTypeCell] at scrutineeSubst
          rw [subst_eitherMatchDependentInlBranchType_iterateLift] at leftBranchSubst
          rw [subst_eitherMatchDependentInrBranchType_iterateLift] at rightBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherMatchCell motive leftBranch rightBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_eitherMatchCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_eitherMatch eitherMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution leftBranch)
                (.childCons (RawTerm.subst substitution rightBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact leftBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact rightBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- idJ row: GENUINE Paulin-Mohring — output `idJMotiveAt motive right witness`; witness at the GENERAL
      -- `idTypeCell typeCode left right`, right endpoint at `typeCode`, base case at the diagonal
      -- `idJMotiveAt motive left (refl left)` (reshaped via `subst_idJMotiveAt_iterateLift` + `subst_reflCell`),
      -- motive obligation under TWO binders (`typeCode`, then `idJMotiveSecondBinderType typeCode left`) at a
      -- universe (its host condition via `SubstHostTyped.consTwice`, its `b`-extended inner binding reshaped via
      -- `subst_iterateLift_idJMotiveSecondBinderType`).
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have rightEndpointSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have baseCaseSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice typeCode
                (idJMotiveSecondBinderType typeCode leftEndpoint) condition)
          rw [subst_idTypeCell] at witnessSubst
          rw [subst_idJMotiveAt_iterateLift, subst_reflCell] at baseCaseSubst
          rw [subst_iterateLift_idJMotiveSecondBinderType, subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (idJCell motive baseCase witness))
            (RawTerm.subst substitution (idJMotiveAt motive rightEndpoint witness))
          rw [subst_idJCell, subst_idJMotiveAt_iterateLift]
          refine HasTypeUnion.elim targetContext .gen_idJ idJElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) motive)
              (.childCons (RawTerm.subst substitution baseCase)
                (.childCons (RawTerm.subst substitution witness) .childNil)))
            (.childCons (RawTerm.subst substitution typeCode)
              (.childCons (RawTerm.subst substitution leftEndpoint)
                (.childCons (RawTerm.subst substitution rightEndpoint) .childNil)))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact witnessSubst
          | tail _ hmem => cases hmem with
            | head => exact rightEndpointSubst
            | tail _ hmem => cases hmem with
              | head => exact baseCaseSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- fst row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (fstCell pairTerm)) (RawTerm.subst substitution firstType)
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          rw [subst_fstCell]
          refine HasTypeUnion.elim targetContext .gen_fst fstElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem with
            | head => exact resultSubst
            | tail _ hmem => cases hmem
      -- snd row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (sndCell pairTerm)) (RawTerm.subst substitution secondType)
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          rw [subst_sndCell]
          refine HasTypeUnion.elim targetContext .gen_snd sndElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem with
            | head => exact resultSubst
            | tail _ hmem => cases hmem
      -- listElim row: DEPENDENT — output `subst0 motive scrutinee`; the nil branch is nullary at
      -- `subst0 motive listNilCell` (reshaped via `subst0_subst_commute`, the closed `listNilCell`
      -- defeq-erases under any substitution), the cons branch at the dependent cons-branch type (reshaped by
      -- `subst_listElimDependentConsBranchType_iterateLift`); motive obligation under one `listTypeCell`
      -- binder (its host condition via `substContextCondition_cons`).  The list (recursive) twin of the
      -- optionMatch row; the second type param is vestigial (fed `elementType`).
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons _resultType .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have nilSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have consSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              _ (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (listTypeCell elementType) substitution condition)
          rw [subst_listTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at nilSubst
          rw [subst_listElimDependentConsBranchType_iterateLift] at consSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_listElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution nilBranch)
                  (.childCons (RawTerm.subst substitution consBranch) .childNil))))
            (.childCons (RawTerm.subst substitution elementType)
              (.childCons (RawTerm.subst substitution elementType) .childNil)) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact nilSubst
            | tail _ hmem => cases hmem with
              | head => exact consSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      intro targetScope targetContext substitution condition
      -- The unified introducer arm (TYTAB-1 collapse): pin the row, destructure the children + type
      -- indices, source each premise's substituted typing from `ihPremises` at the obligation's list
      -- membership, transport the side condition (a `gradedBinderChecks` for the graded rows), then
      -- rebuild through the generic `HasTypeUnion.intro` builder (which threads the `intro` arm at the
      -- matching row).  Same shape as the `elim` arm.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue row : childless value at the pinned type code.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_boolTrue () .childNil))
            (RawTerm.subst substitution boolTypeCell)
          rw [subst_boolTypeCell, RawTerm.subst_mkGen_of_ne_var substitution
            (by intro hit; cases hit)]
          refine HasTypeUnion.intro targetContext .gen_boolTrue boolTrueIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- boolFalse row.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_boolFalse () .childNil))
            (RawTerm.subst substitution boolTypeCell)
          rw [subst_boolTypeCell, RawTerm.subst_mkGen_of_ne_var substitution
            (by intro hit; cases hit)]
          refine HasTypeUnion.intro targetContext .gen_boolFalse boolFalseIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- unit row.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution unitCell) (RawTerm.subst substitution unitTypeCell)
          refine HasTypeUnion.intro targetContext .gen_unit unitIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval0 row.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution intervalZeroCell)
            (RawTerm.subst substitution intervalTypeCell)
          refine HasTypeUnion.intro targetContext .gen_interval0 interval0IntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval1 row.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution intervalOneCell)
            (RawTerm.subst substitution intervalTypeCell)
          refine HasTypeUnion.intro targetContext .gen_interval1 interval1IntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- natZero row.
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution natZeroCell) (RawTerm.subst substitution natTypeCell)
          rw [subst_natTypeCell, subst_natZeroCell]
          refine HasTypeUnion.intro targetContext .gen_natZero natZeroIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- lam row : domain + codomain formation + body under the domain, usage unrestricted.
      · match args, params with
        | .childCons domainCode (.childCons body .childNil), .childCons codomainCode .childNil =>
          have liftedCondition :
              HasTypeUnion.SubstUnionTyped (context.cons domainCode)
                (targetContext.cons (RawTerm.subst substitution domainCode))
                (iterateLiftRaw substitution 1) :=
            HasTypeUnion.SubstUnionTyped.cons domainCode substitution condition
          have domainSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have codomainSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _))
              (targetContext.cons (RawTerm.subst substitution domainCode))
              (iterateLiftRaw substitution 1) liftedCondition
          have bodySubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              (targetContext.cons (RawTerm.subst substitution domainCode))
              (iterateLiftRaw substitution 1) liftedCondition
          rw [subst_universeCodeCell] at domainSubst codomainSubst
          have binderGradedSubst :
              gradedBinderChecks UsageGrade.omega
                (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
            gradedBinderChecks_subst_lift UsageGrade.omega substitution body sideHolds
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (lamCell domainCode body))
            (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
          rw [subst_lamCell, subst_piTyCodeCell]
          refine HasTypeUnion.intro targetContext .gen_lam lamIntroRule
            (.childCons (RawTerm.subst substitution domainCode)
              (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) body) .childNil))
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) .childNil)
            level0 level1 flag rfl binderGradedSubst ?_
          intro obligation hmem
          cases hmem with
          | head => exact domainSubst
          | tail _ hmem => cases hmem with
            | head => exact codomainSubst
            | tail _ hmem => cases hmem with
              | head => exact bodySubst
              | tail _ hmem => cases hmem
      -- pathLam row : interval-pinned domain, body at the weakened carrier, usage affine, no formation.
      · match args, params with
        | .childCons body .childNil, .childCons carrierCode .childNil =>
          have liftedCondition :
              HasTypeUnion.SubstUnionTyped (context.cons intervalTypeCell)
                (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
                (iterateLiftRaw substitution 1) :=
            HasTypeUnion.SubstUnionTyped.cons intervalTypeCell substitution condition
          have bodySubst :=
            ihPremises _ (List.Mem.head _)
              (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
              (iterateLiftRaw substitution 1) liftedCondition
          rw [show RawTerm.weaken carrierCode = RawTerm.rename RawRenaming.weaken carrierCode from rfl,
            subst_iterateLift_one_renameWeaken_commute] at bodySubst
          have binderGradedSubst :
              gradedBinderChecks UsageGrade.one
                (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
            gradedBinderChecks_subst_lift UsageGrade.one substitution body sideHolds
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pathLamCell body))
            (RawTerm.subst substitution
              (bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
                (RawTerm.subst0 body intervalOneCell)))
          rw [subst_pathLamCell, subst_bridgeTypeCell, RawTerm.subst0_subst_commute,
            RawTerm.subst0_subst_commute]
          refine HasTypeUnion.intro targetContext .gen_pathLam pathLamIntroRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) body) .childNil)
            (.childCons (RawTerm.subst substitution carrierCode) .childNil)
            level0 level1 flag rfl binderGradedSubst ?_
          intro obligation hmem
          cases hmem with
          | head =>
              show HasTypeUnion profile (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
                (RawTerm.subst (iterateLiftRaw substitution 1) body)
                (RawTerm.weaken (RawTerm.subst substitution carrierCode))
              rw [show RawTerm.weaken (RawTerm.subst substitution carrierCode)
                    = RawTerm.rename RawRenaming.weaken (RawTerm.subst substitution carrierCode)
                    from rfl]
              exact bodySubst
          | tail _ hmem => cases hmem
      -- natSucc row : a union-recursive child at Nat.
      · match args, params with
        | .childCons child .childNil, .childNil =>
          have childSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_natTypeCell] at childSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natSuccCell child)) (RawTerm.subst substitution natTypeCell)
          rw [subst_natSuccCell, subst_natTypeCell]
          refine HasTypeUnion.intro targetContext .gen_natSucc natSuccIntroRule
            (.childCons (RawTerm.subst substitution child) .childNil) .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact childSubst
          | tail _ hmem => cases hmem
      -- listCons row : grown head at A (homogenized to union) + union-recursive tail at List(A).
      · match args, params with
        | .childCons head (.childCons tail .childNil), .childCons elementType .childNil =>
          have headSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have tailSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_listTypeCell] at tailSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listConsCell head tail))
            (RawTerm.subst substitution (listTypeCell elementType))
          rw [subst_listConsCell, subst_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listCons listConsIntroRule
            (.childCons (RawTerm.subst substitution head)
              (.childCons (RawTerm.subst substitution tail) .childNil))
            (.childCons (RawTerm.subst substitution elementType) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact headSubst
          | tail _ hmem => cases hmem with
            | head => exact tailSubst
            | tail _ hmem => cases hmem
      -- optionSome row : one grown value at the element type, output optionTypeCell.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 .childNil =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionSomeCell value))
            (RawTerm.subst substitution (optionTypeCell typeParam0))
          rw [subst_optionSomeCell, subst_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionSome optionSomeIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem
      -- optionNone row : childless, formedness premise on the free element type.
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          have formSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution optionNoneCell)
            (RawTerm.subst substitution (optionTypeCell typeParam0))
          rw [subst_optionNoneCell, subst_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionNone optionNoneIntroRule .childNil
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact formSubst
          | tail _ hmem => cases hmem
      -- listNil row : the optionNone twin with the list container.
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          have formSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution listNilCell)
            (RawTerm.subst substitution (listTypeCell typeParam0))
          rw [subst_listNilCell, subst_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listNil listNilIntroRule .childNil
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact formSubst
          | tail _ hmem => cases hmem
      -- eitherInl row : grown value at the pinned left, formedness on the free right.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have formSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherInlCell value))
            (RawTerm.subst substitution (eitherTypeCell typeParam0 typeParam1))
          rw [subst_eitherInlCell, subst_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInl eitherInlIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          have leftFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at leftFormSubst
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem with
              | head => exact leftFormSubst
              | tail _ hmem => cases hmem
      -- eitherInr row : grown value pinning the right, free left first in the output.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have formSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherInrCell value))
            (RawTerm.subst substitution (eitherTypeCell typeParam1 typeParam0))
          rw [subst_eitherInrCell, subst_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInr eitherInrIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          have rightFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at rightFormSubst
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem with
              | head => exact rightFormSubst
              | tail _ hmem => cases hmem
      -- pair row : two grown children at two independent type params.
      · match args, params with
        | .childCons child0 (.childCons child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have child0Subst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have child1Subst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have firstFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at firstFormSubst
          have secondFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              targetContext substitution condition
          rw [subst_universeCodeCell] at secondFormSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pairCell child0 child1))
            (RawTerm.subst substitution (productTypeCell typeParam0 typeParam1))
          rw [subst_pairCell, subst_productTypeCell]
          refine HasTypeUnion.intro targetContext .gen_pair pairIntroRule
            (.childCons (RawTerm.subst substitution child0)
              (.childCons (RawTerm.subst substitution child1) .childNil))
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact child0Subst
          | tail _ hmem => cases hmem with
            | head => exact child1Subst
            | tail _ hmem => cases hmem with
              | head => exact firstFormSubst
              | tail _ hmem => cases hmem with
                | head => exact secondFormSubst
                | tail _ hmem => cases hmem
      -- refl row : grown witness, term-indexed Id(typeParam0, witness, witness) output.
      · match args, params with
        | .childCons witness .childNil, .childCons typeParam0 .childNil =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (reflCell witness))
            (RawTerm.subst substitution (idTypeCell typeParam0 witness witness))
          rw [subst_reflCell, subst_idTypeCell]
          refine HasTypeUnion.intro targetContext .gen_refl reflIntroRule
            (.childCons (RawTerm.subst substitution witness) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact witnessSubst
          | tail _ hmem => cases hmem

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
      show HasTypeUnion profile context innerArg
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
          (RawTerm.rename RawRenaming.weaken innerType))
      rw [RawTerm.weaken_subst_cons]
      exact HasTypeUnion.ofGrown innerArgTyped
  | succ tailValue =>
      cases tailValue with
      | zero =>
          show HasTypeUnion profile context outerArg
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken outerType)))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact HasTypeUnion.ofGrown outerArgTyped
      | succ priorValue =>
          show HasTypeUnion profile context
            (variableCell ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken
                (context.lookup ⟨priorValue,
                  Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩))))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact HasTypeUnion.var context ⟨priorValue,
            Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩

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
the bespoke engine could not close is closed here through the union's recursiveElim arm.

UPDATE (TYTAB-2): the union-image binder descent IS now shipped — the transport `UnionSubstPairTransports`
is DISCHARGED UNCONDITIONALLY downstream (`HasTypeUnion.substPairNonDependentUnionImages` in
`HasTypeUnionUnionSubstituent`, wave U3), so the succ subject-reduction rows feed it via
`unionSubstPairTransports` rather than premising it. -/

/-- The recursive call `natElimCell(motive, zeroBranch, succBranch, predecessor)` is union-typed at the
DEPENDENT output `subst0 motive predecessor` — by the union's own `recursiveElim` arm, given the predecessor
union-typed at `Nat`, the zero branch at `subst0 motive natZeroCell`, the step branch at
`natElimDependentSuccBranchType motive` (under the two succ binders), and the motive at `universeCode` (under
one `natTypeCell` binder).  The load-bearing construction closing the recursion loop — the recursive call is
the scrutinee `predecessor` recursed, so its type is the recursor output at `predecessor`. -/
theorem natElimRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (stepBranchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive)) :
    HasTypeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive predecessor) := by
  refine HasTypeUnion.elim context .gen_natElim natElimRule
    (.childCons motive (.childCons zeroBranch (.childCons succBranch (.childCons predecessor .childNil))))
    .childNil resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact predecessorTyped
  | tail _ hmem => cases hmem with
    | head => exact zeroBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact stepBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveFormed
        | tail _ hmem => cases hmem

/-- The `natRec` recursive call is union-typed at `subst0 motive predecessor` — the dependent-recursor twin
of `natElimRecursiveCallUnionTyped`. -/
theorem natRecRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (stepBranchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive)) :
    HasTypeUnion profile context
      (natRecCell motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive predecessor) := by
  refine HasTypeUnion.elim context .gen_natRec natRecElimRule
    (.childCons motive (.childCons zeroBranch (.childCons succBranch (.childCons predecessor .childNil))))
    .childNil resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact predecessorTyped
  | tail _ hmem => cases hmem with
    | head => exact zeroBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact stepBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveFormed
        | tail _ hmem => cases hmem

/-- The union-substituent 2-binder transport for a recursive-eliminator step branch: substitutes the
branch (typed at the twice-weakened result under the two binders) at `var 0 := recursiveCall, var 1 :=
predecessor` with BOTH substituents UNION-typed, yielding the reduct union-typed at `resultType`.  This is
`substPairNonDependent` with a UNION inner substituent — the one ingredient the host
`substPairNonDependent` cannot supply (its inner substituent must be host-typed, and the recursive call is
never host-typed).  Building it needs union-image binder descent (general union weakening); the seed union
defines this abbrev as the succ-ι discharge's input, and TYTAB-2 then DISCHARGES it UNCONDITIONALLY
(`HasTypeUnion.substPairNonDependentUnionImages` in `HasTypeUnionUnionSubstituent`, downstream — wave U3
closes the cumulative former via `unionCumulativeFormerCloses`) — so it is no longer a residual, only a
conduit shape the succ rows are written against. -/
abbrev UnionSubstPairTransports (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (motive : RawTerm (scope + 1)) : Prop :=
  ∀ (branch : RawTerm (scope + 2)) (innerArg outerArg : RawTerm scope),
    HasTypeUnion profile
        ((context.cons natTypeCell).cons motive)
        branch
        (natElimDependentSuccBranchType motive) →
      HasTypeUnion profile context innerArg (RawTerm.subst0 motive outerArg) →
      HasTypeUnion profile context outerArg natTypeCell →
      HasTypeUnion profile context
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
        (RawTerm.subst0 motive (natSuccCell outerArg))

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
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive))
    (unionTransport : UnionSubstPairTransports profile context motive) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive (natSuccCell predecessor)) :=
  ⟨IotaHeadStep.iotaNatElimSucc.toStep,
    unionTransport succBranch
      (natElimCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor
        resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped branchTyped)
      predecessorTyped⟩

/-- **★★ The GENERAL succ-branch natRec ι discharge** — the dependent-recursor twin. -/
theorem natRecSuccIotaComputesTypedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive))
    (unionTransport : UnionSubstPairTransports profile context motive) :
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive (natSuccCell predecessor)) :=
  ⟨IotaHeadStep.iotaNatRecSucc.toStep,
    unionTransport succBranch
      (natRecCell motive zeroBranch succBranch predecessor) predecessor
      branchTyped
      (natRecRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor
        resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped branchTyped)
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
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
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
  /-- The natElim recursive call is union-typed at the dependent output `subst0 motive predecessor` (the
  recursion loop closes), given the dependent zero/step branch typings and the motive formedness. -/
  recursiveCallTyped : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
    HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell resultLevel resultFlag) →
    HasTypeUnion profile context predecessor natTypeCell →
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) →
    HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive) →
    HasTypeUnion profile context
      (natElimCell motive zeroBranch succBranch predecessor) (RawTerm.subst0 motive predecessor)
  /-- The general succ-branch natElim ι discharge holds (given the union-image transport residual), with the
  reduct typed at the dependent output `subst0 motive (natSucc predecessor)`. -/
  succIotaDischarged : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
    HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell resultLevel resultFlag) →
    HasTypeUnion profile context predecessor natTypeCell →
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) →
    HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive) →
    UnionSubstPairTransports profile context motive →
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive (natSuccCell predecessor))

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
    intro _ context motive zeroBranch succBranch predecessor resultLevel resultFlag
      motiveFormed predecessorTyped zeroBranchTyped stepBranchTyped
    exact natElimRecursiveCallUnionTyped context motive zeroBranch succBranch predecessor
      resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped stepBranchTyped
  succIotaDischarged := by
    intro _ context motive zeroBranch succBranch predecessor resultLevel resultFlag
      motiveFormed predecessorTyped zeroBranchTyped branchTyped unionTransport
    exact natElimSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor
      resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped branchTyped
      unionTransport

end FX1Poly.Typed
