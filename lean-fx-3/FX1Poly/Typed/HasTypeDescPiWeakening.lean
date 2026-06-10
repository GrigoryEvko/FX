import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Core.RawTermFresh

/-! # FX1Poly/Typed/HasTypeDescPiWeakening — INTRINSIC renaming/weakening (P6) for the GROWN
    engine `HasTypeDescPi` (formation + Π-intro/elim): its first fibration leg (cartesian lift).

polycell.md §11.8.5 P6: typing is preserved along a context morphism.  This file carries the
RENAMING half for the grown engine — `HasTypeDescPi` is preserved along ANY renaming respecting
the context — and its weakening special case.  It is the cartesian-lift fibration leg of the
grown engine.

## Why the `ofFormation` arm delegates directly

RENAMING preserves formation-ness: renaming introduces no eliminations, so a renamed formation
term is still a formation term.  Hence the `ofFormation` arm delegates DIRECTLY to
`HasTypeDesc.renameRespectingContext` (its context-condition is an EQUALITY, satisfied verbatim)
and re-wraps with `ofFormation` — no closure gap.  (Term-SUBSTITUTION does not preserve
formation-ness — substituting a grown term into a `piTyCodeCell A B`'s component yields a Π type
with a non-formation component — which is why the grown engine carries the native `genFormationPi`
arm that types such results.)

## Structure (mutual recursion: 5 arms + the telescope companion)

A `match`-form MUTUAL recursion, `HasTypeDescPi.renameRespectingContext` ⋈
`DescTelescopePi.renameRespectingTelescope`: the `ofFormation` cross-call is to
`HasTypeDesc.renameRespectingContext` (a separate theorem) on the opaque
`formationTyped`; the other recursions are on strictly-smaller `HasTypeDescPi`/`DescTelescopePi`
sub-derivations (the `genFormationPi` companion cross-call HOISTED before its `by_cases`, so the
spine stays pristine), so Lean's structural recursion lands it without `termination_by`.

* `ofFormation` — delegate to `HasTypeDesc.renameRespectingContext`, re-wrap.
* `conv` — recurse both premises; `rename_universeCodeCell` fixes the reclassifier's universe
  code; `Conv.rename` (#370) renames the conversion.
* `piIntro` (λ) — recurse the domain (its universe code is `rename`-fixed) and the body under the
  lifted renaming, with the one-binder context-condition (`0` → `rename_lift_weaken_commute` on
  the domain; `k+1` → the condition under weakening); reassemble via `rename_{lamCell,piTyCodeCell}`.
* `piElim` (app) — recurse the function (`rename_piTyCodeCell` exposes the renamed Π) and the
  argument; the output commutes by `rename_subst0_commute` (`rename ρ (B[a]) = (B under lift ρ)[a
  under ρ]`); reassemble via `rename_appCell`.  `iterateLiftRaw ρ 1 ≡ RawRenaming.lift ρ` (defeq)
  bridges the codomain forms.
* `genFormationPi` — the GENERIC type-former arm: rename the premise spine through the companion
  `DescTelescopePi.renameRespectingTelescope`, re-fire `genFormationPi` with the renamed children
  (the rule pinned by `DecidableEq Generator`).

## Zero-axiom

Self-recursion + `HasTypeDesc.renameRespectingContext` + `Conv.rename` + the
`rename_{universeCodeCell,piTyCodeCell,lift_weaken_commute,subst0_commute}` bricks + the rfl
`rename_{lamCell,appCell}`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Renaming distributes over the Church-style `lamCell`: the domain annotation (child shift `0`)
is renamed directly, the body (child shift `1`) is renamed under one lift — same `[0, 1]` shape as
`rename_piTyCodeCell`. -/
theorem rename_lamCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (domainAnn : RawTerm sourceScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming (lamCell domainAnn body)
      = lamCell (RawTerm.rename rawRenaming domainAnn)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) :=
  rfl

/-- Renaming distributes over `appCell`: both children (shifts `[0, 0]`) are renamed directly. -/
theorem rename_appCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argument : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (appCell functionTerm argument)
      = appCell (RawTerm.rename rawRenaming functionTerm)
          (RawTerm.rename rawRenaming argument) :=
  rfl

/-- The one-binder lift of a renaming context-condition: if `rawRenaming` respects the context,
its single lift respects the context extended by `domainCode` (renamed).  The binder-crossing
condition the `piIntro` arm of `renameRespectingContext` needs (the lone non-telescope
binder-crosser; `genFormationPi` crosses binders via its telescope companion) — `0` resolves by
`rename_lift_weaken_commute` on the domain, `k+1` by the base condition under weakening
(`iterateLiftRaw ρ 1 ≡ RawRenaming.lift ρ` defeq throughout). -/
theorem renameContextCondition_cons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (rawRenaming : RawRenaming sourceScope targetScope)
    (contextCondition : ∀ index : Fin sourceScope,
      RawTerm.rename rawRenaming (sourceContext.lookup index)
        = targetContext.lookup (rawRenaming index)) :
    ∀ index : Fin (sourceScope + 1),
      RawTerm.rename (iterateLiftRaw rawRenaming 1)
          ((sourceContext.cons domainCode).lookup index)
        = (targetContext.cons (RawTerm.rename rawRenaming domainCode)).lookup
            (iterateLiftRaw rawRenaming 1 index) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show RawTerm.rename (iterateLiftRaw rawRenaming 1)
          (RawTerm.rename RawRenaming.weaken domainCode)
        = RawTerm.rename RawRenaming.weaken (RawTerm.rename rawRenaming domainCode)
      exact rename_lift_weaken_commute rawRenaming domainCode
  | succ k =>
      show RawTerm.rename (iterateLiftRaw rawRenaming 1)
          (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        = RawTerm.rename RawRenaming.weaken
            (targetContext.lookup (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
      exact (rename_lift_weaken_commute rawRenaming
          (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)).trans
        (congrArg (RawTerm.rename RawRenaming.weaken)
          (contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))

mutual

/-- INTRINSIC renaming for the grown engine: `HasTypeDescPi` is preserved along any renaming that
respects the context (sends each source binding's looked-up type to the target's, commuting with
`rename`), with subject and classifier renamed.  The grown engine's cartesian-lift fibration leg.
The `ofFormation` cross-call routes through the intrinsic `HasTypeDesc.renameRespectingContext`. -/
theorem HasTypeDescPi.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescPi profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext rawRenaming contextCondition =>
      HasTypeDescPi.ofFormation
        (formationTyped.renameRespectingContext targetContext rawRenaming contextCondition)
  | .conv levelExpr flag typed converts reclassifierTyped =>
      fun targetContext rawRenaming contextCondition => by
        have typedRenamed :=
          HasTypeDescPi.renameRespectingContext typed targetContext rawRenaming contextCondition
        have reclassifierRenamed :=
          HasTypeDescPi.renameRespectingContext reclassifierTyped targetContext rawRenaming
            contextCondition
        rw [rename_universeCodeCell] at reclassifierRenamed
        exact HasTypeDescPi.conv levelExpr flag typedRenamed
          (Conv.rename rawRenaming converts) reclassifierRenamed
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext rawRenaming contextCondition => by
      have domainRenamed :=
        HasTypeDescPi.renameRespectingContext domainTyped targetContext rawRenaming
          contextCondition
      rw [rename_universeCodeCell] at domainRenamed
      have codomainRenamed :=
        HasTypeDescPi.renameRespectingContext codomainTyped
          (targetContext.cons (RawTerm.rename rawRenaming domainCode))
          (iterateLiftRaw rawRenaming 1)
          (renameContextCondition_cons domainCode rawRenaming contextCondition)
      rw [rename_universeCodeCell] at codomainRenamed
      have bodyRenamed :=
        HasTypeDescPi.renameRespectingContext bodyTyped
          (targetContext.cons (RawTerm.rename rawRenaming domainCode))
          (iterateLiftRaw rawRenaming 1)
          (renameContextCondition_cons domainCode rawRenaming contextCondition)
      rw [rename_lamCell, rename_piTyCodeCell]
      exact HasTypeDescPi.piIntro domainLevel codomainLevel flag domainRenamed codomainRenamed
        bodyRenamed
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => fun targetContext rawRenaming contextCondition => by
      have functionRenamed :=
        HasTypeDescPi.renameRespectingContext functionTyped targetContext rawRenaming
          contextCondition
      rw [rename_piTyCodeCell] at functionRenamed
      have argumentRenamed :=
        HasTypeDescPi.renameRespectingContext argumentTyped targetContext rawRenaming
          contextCondition
      rw [rename_appCell, RawTerm.rename_subst0_commute]
      exact HasTypeDescPi.piElim functionRenamed argumentRenamed
  | .genFormationPi _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext rawRenaming contextCondition => by
      -- Cross-call the telescope companion on the PRISTINE `premises` FIRST (before any
      -- `by_cases`), so structural recursion recognises it as a sub-derivation — the same hoist
      -- discipline the formation `genFormation` arm uses.  The generic arm renames generically:
      -- no per-former dispatch beyond pinning the rule, the §11.8.5 cascade-free shape.
      have renamedPremises :=
        DescTelescopePi.renameRespectingTelescope premises targetContext rawRenaming
          contextCondition
      -- ROW-SHAPE-AGNOSTIC (no `by_cases pi/sigma`, no concrete `rule`): the grown-engine rename twin.
      -- `typingRuleDescOf_output_renameStable` rewrites the ABSTRACT rule's output through the renaming
      -- (universe codes are scope-polymorphic leaves for every row shape, including a future flag-pinned
      -- nullary row), the non-var commutation `RawTerm.rename_mkGen_of_ne_var` distributes the renaming over
      -- the ABSTRACT formation cell, and the GENERIC `genFormationPi` re-fires with the ORIGINAL abstract
      -- rule/generator/isFormation — realizing the "no per-former dispatch" cascade-free shape this arm's
      -- docstring describes.
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_renameStable isFormation rawRenaming levels flag,
        RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
      exact HasTypeDescPi.genFormationPi targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) levels flag
        rule isFormation renamedPremises

theorem DescTelescopePi.renameRespectingTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (rawRenaming : RawRenaming baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        RawTerm.rename (iterateLiftRaw rawRenaming currentDepth)
            (sourceContext.lookup index)
          = targetContext.lookup (iterateLiftRaw rawRenaming currentDepth index)) →
      DescTelescopePi profile targetContext levels flag
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _rawRenaming _contextCondition =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :
            HasTypeDescPi profile targetContext
              (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headRenamed :=
            HasTypeDescPi.renameRespectingContext headTyped targetContext
              (iterateLiftRaw rawRenaming currentDepth) contextCondition
          rwa [rename_universeCodeCell] at headRenamed
        refine DescTelescopePi.cons targetContext
          (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head) headLevel
          restLevels flag (RawTermChildren.rename rawRenaming rest) renamedHeadTyped ?_
        refine DescTelescopePi.renameRespectingTelescope restTyped
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
            exact (rename_lift_weaken_commute (iterateLiftRaw rawRenaming currentDepth)
                (_sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)).trans
              (congrArg (RawTerm.rename RawRenaming.weaken)
                (contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))

end

/-- INTRINSIC weakening for the grown engine: a `HasTypeDescPi` derivation survives extending the
context by one fresh binding, subject and classifier shifted by `RawRenaming.weaken`.  The
corollary of `renameRespectingContext` whose context-condition holds DEFINITIONALLY
(`fun _ => rfl`): `weaken index` is `Fin.succ index`, the `cons` `lookup` fires its successor arm. -/
theorem HasTypeDescPi.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (newBinding : RawTerm scope)
    (derivation : HasTypeDescPi profile context subject classifier) :
    HasTypeDescPi profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
