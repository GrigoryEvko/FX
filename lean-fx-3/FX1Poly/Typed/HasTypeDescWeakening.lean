import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescWeakening — INTRINSIC renaming/weakening (P6) for the
    description engine.

polycell.md §11.8.5 P6 ("Substitution / weakening = whiskering, the β-engine"): typing is
preserved along a context morphism.  This file ships the renaming half — `HasTypeDesc` is
preserved along ANY renaming that respects the context (sends each source binding's
looked-up type to the target's, commuting with `rename`), and its weakening special case.

## Intrinsic — the first clean mutual `HasTypeDesc` metatheorem of the DECOUPLE

`HasTypeDesc` is MUTUAL with `DescTelescope`, so this is a MUTUAL recursion — but unlike
the deferred full-intrinsic P7 uniqueness, it has NO second-derivation inversion, so the
cross-calls sit on PRISTINE `match`-bound subterms (`typedPremise`, `premises`, `headTyped`)
exactly like the proven `HasTypeDesc.toHasType` ⋈ `DescTelescope.toHasTypeTelescope` pair.
Lean's structural recursion lands it directly (no `termination_by` needed) once the
genFormation arm's companion cross-call is HOISTED before the `by_cases` (so `premises` is
still pristine — the same discipline `toHasType` uses).  Proved BY INDUCTION on
`HasTypeDesc`, NOT routed through `HasType` — the first intrinsic-by-induction metatheorem
of the decouple (validity/inversion/uniqueness were case-analysis; this is genuine
recursion).

## The telescope companion

`DescTelescope.renameRespectingTelescope` renames the premise spine.  Its context-condition
is stated at the telescope's `currentDepth` via `iterateLiftRaw rawRenaming currentDepth`;
the `cons` arm fires the head recursion with that depth-`cd` renaming (the condition passes
verbatim), and recurses on the tail at depth `cd+1` with the LIFTED condition — the
N-binder generalization of the bespoke `HasType.renameRespectingContext`'s single-binder
`piFormation` codomain handling.  `iterateLiftRaw ρ (cd+1) ≡ RawRenaming.lift (iterateLiftRaw
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
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        show HasTypeDesc profile targetContext
          (RawTerm.rename rawRenaming (RawTerm.mkGen .gen_piTyCode payload children))
          (RawTerm.rename rawRenaming (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact HasTypeDesc.genFormation targetContext .gen_piTyCode payload
          (RawTermChildren.rename rawRenaming children) levels flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode renamedPremises
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          obtain rfl : rule = { outputType := universeFormerOutput } :=
            Option.some.inj isFormation.symm
          show HasTypeDesc profile targetContext
            (RawTerm.rename rawRenaming (RawTerm.mkGen .gen_sigmaTyCode payload children))
            (RawTerm.rename rawRenaming (universeCodeCell (lmaxAll levels) flag))
          rw [rename_universeCodeCell]
          exact HasTypeDesc.genFormation targetContext .gen_sigmaTyCode payload
            (RawTermChildren.rename rawRenaming children) levels flag
            { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode renamedPremises
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

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
`rename weaken (context.lookup index)`.  Decoupled from `HasType` (no route through the
`⟺` soundness/completeness maps). -/
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
