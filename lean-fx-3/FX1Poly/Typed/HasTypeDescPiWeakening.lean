import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Core.RawTermFresh

/-! # FX1Poly/Typed/HasTypeDescPiWeakening — INTRINSIC renaming/weakening (P6) for the GROWN
    engine `HasTypeDescPi` (formation + Π-intro/elim): its first fibration leg (cartesian lift).

polycell.md §11.8.5 P6: typing is preserved along a context morphism.  This file ships the
RENAMING half for the grown engine — `HasTypeDescPi` is preserved along ANY renaming respecting
the context — and its weakening special case.  It is the first of the two grown-engine fibration
legs; the substitution leg (the grown β-engine) follows once the engine is made
substitution-closed (it needs a native Π-formation arm, since term-substitution into a Π type's
component can produce a Π type with a non-formation component — see below).

## Why renaming is clean now, but substitution is NOT (yet)

RENAMING preserves formation-ness: renaming introduces no eliminations, so a renamed formation
term is still a formation term.  Hence the `ofFormation` arm delegates DIRECTLY to the shipped
`HasTypeDesc.renameRespectingContext` (its context-condition is an EQUALITY, satisfied verbatim)
and re-wraps with `ofFormation` — no closure gap.  Term-SUBSTITUTION is different: substituting a
grown term (e.g. an application) into a `piTyCodeCell A B`'s component yields a Π type with a
non-formation component, which `ofFormation` cannot type (the grown engine currently forms Π
types only via `ofFormation`).  So the substitution leg awaits a native Π-formation arm; renaming
does not, and lands fully here.

## Structure (self-recursion, four arms)

A `match`-form self-recursion (NOT mutual): the `ofFormation` cross-call is to the shipped
`HasTypeDesc.renameRespectingContext` (a different, completed theorem) on the opaque
`formationTyped`; the only recursions are on the strictly-smaller `HasTypeDescPi`
sub-derivations, so Lean's structural recursion lands it without `termination_by`.

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

## Zero-axiom

Self-recursion + the shipped `HasTypeDesc.renameRespectingContext` + `Conv.rename` + the reused
`rename_{universeCodeCell,piTyCodeCell,lift_weaken_commute,subst0_commute}` bricks + the rfl
`rename_{lamCell,appCell}`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Renaming distributes over `lamCell`: the body (child shift `1`) is renamed under one lift. -/
theorem rename_lamCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming (lamCell body)
      = lamCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) :=
  rfl

/-- Renaming distributes over `appCell`: both children (shifts `[0, 0]`) are renamed directly. -/
theorem rename_appCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argument : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (appCell functionTerm argument)
      = appCell (RawTerm.rename rawRenaming functionTerm)
          (RawTerm.rename rawRenaming argument) :=
  rfl

/-- INTRINSIC renaming for the grown engine: `HasTypeDescPi` is preserved along any renaming that
respects the context (sends each source binding's looked-up type to the target's, commuting with
`rename`), with subject and classifier renamed.  The grown engine's cartesian-lift fibration leg.
Decoupled from `HasType` — the `ofFormation` cross-call routes through the intrinsic
`HasTypeDesc.renameRespectingContext`, not the `⟺` soundness map. -/
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
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel domainFlag
      domainTyped bodyTyped => fun targetContext rawRenaming contextCondition => by
      have domainRenamed :=
        HasTypeDescPi.renameRespectingContext domainTyped targetContext rawRenaming
          contextCondition
      rw [rename_universeCodeCell] at domainRenamed
      have bodyRenamed :=
        HasTypeDescPi.renameRespectingContext bodyTyped
          (targetContext.cons (RawTerm.rename rawRenaming domainCode))
          (iterateLiftRaw rawRenaming 1) (by
            intro index
            obtain ⟨indexValue, indexBound⟩ := index
            cases indexValue with
            | zero =>
                show RawTerm.rename (iterateLiftRaw rawRenaming 1)
                    (RawTerm.rename RawRenaming.weaken domainCode)
                  = RawTerm.rename RawRenaming.weaken
                      (RawTerm.rename rawRenaming domainCode)
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
                    (contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [rename_lamCell, rename_piTyCodeCell]
      exact HasTypeDescPi.piIntro domainLevel domainFlag domainRenamed bodyRenamed
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

/-- INTRINSIC weakening for the grown engine: a `HasTypeDescPi` derivation survives extending the
context by one fresh binding, subject and classifier shifted by `RawRenaming.weaken`.  The
corollary of `renameRespectingContext` whose context-condition holds DEFINITIONALLY
(`fun _ => rfl`): `weaken index` is `Fin.succ index`, the `cons` `lookup` fires its successor arm.
Decoupled from `HasType`. -/
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
