import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.CellRenaming
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Typed/HasTypeDescWeakening — INTRINSIC renaming/weakening (P6) for the
    description engine.

polycell.md §11.8.5 P6 ("Substitution / weakening = whiskering, the β-engine"): typing is
preserved along a context morphism.  This file carries the renaming half — `HasTypeDesc` is
preserved along ANY renaming that respects the context (sends each source binding's
looked-up type to the target's, commuting with `rename`), and its weakening special case.

## Intrinsic mutual `HasTypeDesc` recursion (the DECOUPLE)

`HasTypeDesc` is MUTUAL with `DescTelescope`, so this is a MUTUAL recursion — and unlike
the P7 uniqueness recursion, it has NO second-derivation inversion, so the cross-calls sit
on PRISTINE `match`-bound subterms (`typedPremise`, `premises`, `headTyped`).  Lean's structural
recursion lands it directly (no `termination_by` needed) once the genFormation arm's
companion cross-call is HOISTED before the `by_cases` (so `premises` is still pristine).
Proved BY INDUCTION on `HasTypeDesc` (validity/inversion/uniqueness are case-analysis; this is genuine
recursion).

## The telescope companion

`DescTelescope.renameRespectingTelescope` renames the premise spine.  Its context-condition
is stated at the telescope's `currentDepth` via `iterateLiftRaw rawRenaming currentDepth`;
the `cons` arm fires the head recursion with that depth-`cd` renaming (the condition passes
verbatim), and recurses on the tail at depth `cd+1` with the LIFTED condition — the
N-binder generalization of single-binder `piFormation` codomain handling.
`iterateLiftRaw ρ (cd+1) ≡ RawRenaming.lift (iterateLiftRaw
ρ cd)` (`iterateLiftRaw_succ_unfolds`, defeq), so the lifted condition reduces to
`rename_lift_weaken_commute` on each looked-up type at every depth.

## Zero-axiom

Mutual structural recursion + the reused `rename_{variableCell,universeCodeCell}` /
`rename_lift_weaken_commute` bricks + `Conv.rename` (#370) + the nested-`if` generator pin
(propext-free via `DecidableEq Generator`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Row-shape-agnostic output rename-stability**: renaming a formation
rule's output at the source scope yields the output at the target scope — universe codes are
scope-polymorphic leaves, for EVERY row shape (the flag-using `universeFormerOutput` rows and
the flag-pinned nullary `gen_unitCode` row alike).  Consumers use this instead of the strong
`formationRuleIsUniverseFormer` equation, which the nullary row falsifies. -/
theorem typingRuleDescOf_output_renameStable {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat} (rawRenaming : RawRenaming sourceScope targetScope)
    (levels : List LevelExpr) (flag : UniverseFlag) :
    RawTerm.rename rawRenaming (rule.outputType sourceScope levels flag)
      = rule.outputType targetScope levels flag := by
  rw [typingRuleDescOf_output_eq_outputData isFormation sourceScope levels flag,
    typingRuleDescOf_output_eq_outputData isFormation targetScope levels flag]
  exact rename_universeCodeCell rawRenaming
    (formationOutputData generator levels flag).1
    (formationOutputData generator levels flag).2

mutual

theorem HasTypeDesc.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDesc profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) :=
  match derivation with
  | .var _sourceContext index => fun targetContext rawRenaming contextCondition => by
      rw [rename_variableCell, contextCondition index]
      exact HasTypeDesc.var targetContext (rawRenaming index)
  | .conv levelExpr flag typedPremise converts reclassifierTyped =>
      fun targetContext rawRenaming contextCondition => by
        have premiseTyped :=
          HasTypeDesc.renameRespectingContext typedPremise targetContext rawRenaming
            contextCondition
        have reclassifierTypedRenamed :=
          HasTypeDesc.renameRespectingContext reclassifierTyped targetContext rawRenaming
            contextCondition
        rw [rename_universeCodeCell] at reclassifierTypedRenamed
        exact HasTypeDesc.conv levelExpr flag premiseTyped
          (Conv.rename rawRenaming converts) reclassifierTypedRenamed
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext rawRenaming _contextCondition => by
        rw [rename_universeCodeCell, rename_universeCodeCell]
        exact HasTypeDesc.universeFormation targetContext levelExpr flag
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext rawRenaming contextCondition => by
      -- Cross-call the telescope companion on the PRISTINE `premises` FIRST (before any
      -- `by_cases`), so structural recursion recognises it as a sub-derivation — exactly
      -- as `HasTypeDesc.toHasType` calls `toHasTypeTelescope premises` up front.  The
      -- renamed premises do not depend on the generator, so this hoist is sound.
      have renamedPremises :=
        DescTelescope.renameRespectingTelescope premises targetContext rawRenaming
          contextCondition
      -- ROW-SHAPE-AGNOSTIC (no `by_cases pi/sigma`, no concrete `rule`): the rename twin of the
      -- substitution migration.  `formationRuleImpliesNotVariable` discharges the non-`gen_var` side
      -- condition, `typingRuleDescOf_output_renameStable` rewrites the ABSTRACT rule's output through
      -- the renaming (universe codes are scope-polymorphic leaves for every row shape — the flag-using
      -- `universeFormerOutput` rows and any future flag-pinned nullary row alike), and
      -- `RawTerm.rename_mkGen_of_ne_var` distributes the renaming over the ABSTRACT formation cell.  A new
      -- formation row (including a flag-pinned nullary one) absorbs here with zero edits — reconstruction
      -- carries the ORIGINAL abstract `rule`/`generator`/`isFormation`.
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_renameStable isFormation rawRenaming levels flag,
        RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
      exact HasTypeDesc.genFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) levels flag
        rule isFormation renamedPremises

theorem DescTelescope.renameRespectingTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (rawRenaming : RawRenaming baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        RawTerm.rename (iterateLiftRaw rawRenaming currentDepth)
            (sourceContext.lookup index)
          = targetContext.lookup (iterateLiftRaw rawRenaming currentDepth index)) →
      DescTelescope profile targetContext levels flag
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _rawRenaming _contextCondition =>
      DescTelescope.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headRenamed :=
            HasTypeDesc.renameRespectingContext headTyped targetContext
              (iterateLiftRaw rawRenaming currentDepth) contextCondition
          rwa [rename_universeCodeCell] at headRenamed
        refine DescTelescope.cons targetContext
          (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head) headLevel
          restLevels flag (RawTermChildren.rename rawRenaming rest) renamedHeadTyped ?_
        refine DescTelescope.renameRespectingTelescope restTyped
          (targetContext.cons
            (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head))
          rawRenaming ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show RawTerm.rename (iterateLiftRaw rawRenaming (currentDepth + 1))
                (RawTerm.rename RawRenaming.weaken head)
              = RawTerm.rename RawRenaming.weaken
                  (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head)
            exact rename_lift_weaken_commute
              (iterateLiftRaw rawRenaming currentDepth) head
        | succ k =>
            show RawTerm.rename (iterateLiftRaw rawRenaming (currentDepth + 1))
                (RawTerm.rename RawRenaming.weaken
                  (_sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
              = RawTerm.rename RawRenaming.weaken
                  (targetContext.lookup
                    (iterateLiftRaw rawRenaming currentDepth
                      ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
            -- `iterateLiftRaw ρ (cd+1) ≡ RawRenaming.lift (iterateLiftRaw ρ cd)` (defeq,
            -- via `iterateLiftRaw_succ_unfolds`), so the lift-weaken commutation applies
            -- through `.trans` (defeq on its LHS); then `contextCondition` rewrites the
            -- looked-up type under the weakening.
            exact (rename_lift_weaken_commute (iterateLiftRaw rawRenaming currentDepth)
                (_sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)).trans
              (congrArg (RawTerm.rename RawRenaming.weaken)
                (contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))

end

/-- INTRINSIC typed weakening (P6, the cartesian-lift skeleton of the fibration) for the
description engine: a `HasTypeDesc` derivation survives extending the context by one fresh
binding, with subject and classifier shifted by `RawRenaming.weaken`.  The corollary of
`renameRespectingContext` whose context-condition holds DEFINITIONALLY (`fun _ => rfl`):
`weaken index` is `Fin.succ index`, the `cons` telescope's `lookup` fires its successor
arm, and the `Fin` proof collapses by proof-irrelevance — leaving exactly
`rename weaken (context.lookup index)`. -/
theorem HasTypeDesc.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (newBinding : RawTerm scope)
    (derivation : HasTypeDesc profile context subject classifier) :
    HasTypeDesc profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
