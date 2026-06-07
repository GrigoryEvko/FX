import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescWeakening

/-! # FX1Poly/Typed/HasTypeDescFlatWeakening
    — INTRINSIC renaming/weakening (P6) for the flat-former typing judgment

`HasTypeDescFlat` (the standalone flat-former engine, #934) types the non-dependent `[0,0]` type-code formers
`product` / `sum` / `either` / `arrow` / `equiv`.  These are type CODES — they can appear in OPEN contexts (e.g.
`product A B` with `A`, `B` type variables), so the flat engine needs the same structural metatheory the
cumulative engine has: typing is preserved along any context morphism (renaming) and under context extension
(weakening).  This file supplies it — the flat twin of `HasTypeDescWeakening` (`HasTypeDesc.renameRespectingContext`
/ `weakenUnderBinding`).

## Lighter than the cumulative renaming

`DescTelescope.renameRespectingTelescope` must thread `iterateLiftRaw rawRenaming currentDepth` through each
child (the cumulative telescope EXTENDS the context per child, so the renaming is lifted at each depth and the
tail recurses at `currentDepth + 1` with the LIFTED context-condition).  The flat telescope does NONE of that:
`FlatDescTelescope` keeps every sibling at the SAME base context (shift 0), so `FlatDescTelescope.renameRespectingTelescope`
renames each head with the BASE `rawRenaming` (no `iterateLiftRaw`) and the tail recurses with the SAME
context-condition — no lift, no depth bookkeeping.  This is the renaming-side manifestation of the same
structural economy seen in the flat SR (firing-45, no `convTelescope`) and flat SN (firing-46, non-mutual
children-SN).

The cell-reconstruction arm is identical in shape to the cumulative one: `flatFormationRuleImpliesNotVariable`
discharges the `≠ gen_var` side condition, `flatFormationRuleIsUniverseFormer` makes `rule` concrete via
`obtain rfl`, and `RawTerm.rename_mkGen_of_ne_var` distributes the renaming over the abstract flat cell — so a
future flat row absorbs here with no edit (table-generic, like the cumulative rename twin).

## Zero-axiom verification

`FlatDescTelescope.renameRespectingTelescope` is structural `match`-recursion reusing
`HasTypeDesc.renameRespectingContext` on each head.  `HasTypeDescFlat.renameRespectingContext` is a single-arm
`cases derivation` + the two flat former-table helpers + `RawTerm.rename_mkGen_of_ne_var` +
`Generator.payload_scope_invariant_of_not_var`.  `weakenUnderBinding` instantiates at `RawRenaming.weaken` with
the definitionally-true context-condition (`fun _ => rfl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Flat telescope renaming.**  Re-types the flat premise spine along a context-respecting renaming.  SIMPLER
than `DescTelescope.renameRespectingTelescope`: the flat `cons` does NOT extend the context, so the
context-condition stays at the base `rawRenaming` (no `iterateLiftRaw`) and the tail recurses with the SAME
condition.  Structural `match`-recursion reusing `HasTypeDesc.renameRespectingContext` on each head child. -/
theorem FlatDescTelescope.renameRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming scope targetScope),
      (∀ index : Fin scope,
        RawTerm.rename rawRenaming (context.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      FlatDescTelescope profile targetContext flag levels
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil => fun targetContext _rawRenaming _contextCondition => FlatDescTelescope.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.rename rawRenaming head)
              (universeCodeCell headLevel flag) := by
          have headRenamed :=
            HasTypeDesc.renameRespectingContext headTyped targetContext rawRenaming contextCondition
          rwa [rename_universeCodeCell] at headRenamed
        exact FlatDescTelescope.cons (RawTerm.rename rawRenaming head) headLevel restLevels
          (RawTermChildren.rename rawRenaming rest) renamedHeadTyped
          (FlatDescTelescope.renameRespectingTelescope restTyped targetContext rawRenaming
            contextCondition)

/-- **Flat-former renaming.**  A `HasTypeDescFlat` derivation is preserved along any context-respecting
renaming — the flat twin of `HasTypeDesc.renameRespectingContext`.  Single-arm `cases` reusing the flat
telescope rename; the flat cell reconstructs table-generically via `RawTerm.rename_mkGen_of_ne_var`. -/
theorem HasTypeDescFlat.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescFlat profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescFlat profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      intro targetScope targetContext rawRenaming contextCondition
      have renamedPremise :=
        FlatDescTelescope.renameRespectingTelescope premise targetContext rawRenaming contextCondition
      have hNotVar : generator ≠ Generator.gen_var := flatFormationRuleImpliesNotVariable isFlat
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        flatFormationRuleIsUniverseFormer isFlat
      show HasTypeDescFlat profile targetContext
        (RawTerm.rename rawRenaming (RawTerm.mkGen generator payload children))
        (RawTerm.rename rawRenaming (universeFormerOutput sourceScope levels flag))
      rw [show universeFormerOutput sourceScope levels flag
            = universeCodeCell (lmaxAll levels) flag from rfl, rename_universeCodeCell,
          RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
      exact HasTypeDescFlat.flatFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) levels flag
        { outputType := universeFormerOutput } isFlat renamedPremise

/-- **Flat-former weakening.**  A `HasTypeDescFlat` derivation survives extending the context by one fresh
binding, with subject and classifier shifted by `RawRenaming.weaken` — the flat twin of
`HasTypeDesc.weakenUnderBinding`.  The corollary of `renameRespectingContext` whose context-condition holds
DEFINITIONALLY (`fun _ => rfl`). -/
theorem HasTypeDescFlat.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (derivation : HasTypeDescFlat profile context subject classifier) :
    HasTypeDescFlat profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken (fun _ => rfl)

end FX1Poly.Typed
