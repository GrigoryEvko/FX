import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeDescFlatSubstitution
    — INTRINSIC substitution (P6, the β-engine) for the flat-former typing judgment

`HasTypeDescFlat` (the standalone flat-former engine, #934) types the non-dependent `[0,0]` type-code formers
`product` / `sum` / `either` / `arrow` / `equiv`.  After renaming/weakening (firing-47,
`HasTypeDescFlatWeakening`), the substitution half completes the flat engine's P6 structural metatheory: typing is
preserved along any substitution whose substituents are target-typed.  This file supplies it — the flat twin of
`HasTypeDescSubstitution` (`HasTypeDesc.substRespectingContext` / `substituteUnderBinding`, the corollary the β-rule
cites).

## Dramatically lighter than the cumulative substitution

`DescTelescope.substRespectingTelescope` threads `iterateLiftRaw substitution currentDepth` through each child and
its `cons` arm recurses on the tail at `currentDepth + 1` with the LIFTED substitution-condition, whose `0` /
successor split needs a fresh `var` at `0` and the substituent WEAKENED across the binder (via the intrinsic
`HasTypeDesc.weakenUnderBinding`).  The flat telescope does NONE of that: `FlatDescTelescope` keeps every sibling
at the SAME base context (shift 0), so `FlatDescTelescope.substRespectingTelescope` substitutes each head with the
BASE `substitution` and the tail recurses with the SAME substitution-condition — no `iterateLiftRaw`, no `0` /
successor split, no `weakenUnderBinding`.  The entire successor-case machinery of the cumulative companion
vanishes.  (The same structural economy as the flat SR, SN, and weakening: flat siblings never bind.)

The `subst0` corollary `substituteUnderBinding`, by contrast, mirrors the cumulative proof EXACTLY: its
side-condition concerns the AMBIENT context's lookups (typed in the main `HasTypeDesc` engine), not the flat
telescope, so the `0` / successor singleton split is identical.

## Zero-axiom verification

`FlatDescTelescope.substRespectingTelescope` is structural `match`-recursion reusing
`HasTypeDesc.substRespectingContext` on each head.  `HasTypeDescFlat.substRespectingContext` is a single-arm `cases`
+ the two flat former-table helpers (firing-47) + `RawTerm.subst_mkGen_of_ne_var` +
`Generator.payload_scope_invariant_of_not_var`.  `substituteUnderBinding` instantiates at `RawTermSubst.singleton`
with the `subst_singleton_renameWeaken_cancel` brick.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Flat telescope substitution.**  Re-types the flat premise spine along a substitution whose substituents are
target-typed.  Dramatically SIMPLER than `DescTelescope.substRespectingTelescope`: the flat `cons` does NOT extend
the context, so NO `iterateLiftRaw`, NO `0` / successor split, NO `weakenUnderBinding` — the tail recurses with the
SAME substitution-condition.  Structural `match`-recursion reusing `HasTypeDesc.substRespectingContext` on each head. -/
theorem FlatDescTelescope.substRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst scope targetScope),
      (∀ index : Fin scope,
        HasTypeDesc profile targetContext (substitution index)
          (RawTerm.subst substitution (context.lookup index))) →
      FlatDescTelescope profile targetContext flag levels
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil => fun targetContext _substitution _substitutionTyped => FlatDescTelescope.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.subst substitution head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDesc.substRespectingContext headTyped targetContext substitution substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        exact FlatDescTelescope.cons (RawTerm.subst substitution head) headLevel restLevels
          (RawTermChildren.subst substitution rest) substHeadTyped
          (FlatDescTelescope.substRespectingTelescope restTyped targetContext substitution
            substitutionTyped)

/-- **Flat-former substitution.**  A `HasTypeDescFlat` derivation is preserved along any well-typed substitution
— the flat twin of `HasTypeDesc.substRespectingContext`.  Single-arm `cases` reusing the flat telescope subst; the
flat cell reconstructs table-generically via `RawTerm.subst_mkGen_of_ne_var`. -/
theorem HasTypeDescFlat.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescFlat profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDesc profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescFlat profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      intro targetScope targetContext substitution substitutionTyped
      have substPremise :=
        FlatDescTelescope.substRespectingTelescope premise targetContext substitution substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var := flatFormationRuleImpliesNotVariable isFlat
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        flatFormationRuleIsUniverseFormer isFlat
      show HasTypeDescFlat profile targetContext
        (RawTerm.subst substitution (RawTerm.mkGen generator payload children))
        (RawTerm.subst substitution (universeFormerOutput sourceScope levels flag))
      rw [show universeFormerOutput sourceScope levels flag
            = universeCodeCell (lmaxAll levels) flag from rfl, subst_universeCodeCell,
          RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact HasTypeDescFlat.flatFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) levels flag
        { outputType := universeFormerOutput } isFlat substPremise

/-- **Flat-former single-substitution (the β-engine).**  Substituting a well-typed `argument` for de Bruijn 0
preserves `HasTypeDescFlat` — the flat twin of `HasTypeDesc.substituteUnderBinding`, the corollary the β-rule
`app(lam(b), a) ↝ b[a]` cites for a flat-former-typed subject.  Its side-condition concerns the AMBIENT context's
lookups (typed in the main `HasTypeDesc` engine), so the `0` / successor singleton split mirrors the cumulative
proof exactly. -/
theorem HasTypeDescFlat.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)} (argument : RawTerm scope)
    (derivation : HasTypeDescFlat profile (context.cons argType) subject classifier)
    (argumentTyped : HasTypeDesc profile context argument argType) :
    HasTypeDescFlat profile context
      (RawTerm.subst0 subject argument)
      (RawTerm.subst0 classifier argument) := by
  refine derivation.substRespectingContext context (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDesc profile context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken argType))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ k =>
      show HasTypeDesc profile context
          (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact HasTypeDesc.var context ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩

end FX1Poly.Typed
