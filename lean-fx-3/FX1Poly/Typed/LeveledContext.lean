import FX1Poly.Typed.FundamentalLevelIndexed

/-! # FX1Poly/Typed/LeveledContext
    — the leveled valid-context structure for the dependent fundamental theorem's recursor motive

The level-indexed term fundamental theorem (`FundamentalLevelIndexed.lean`) has all its per-constructor arms
shipped as standalone lemmas (var / universeFormation / piElim / conv / piIntro / former), and the type half
is a `tarskiDecode` projection of the term half (`typeFundamentalOfTermFundamental`).  The remaining work is
the `HasTypeDescPi.rec` ASSEMBLY, whose motive must thread a per-variable level vector `contextLevels` so that
`var` concludes at its own env level while `conv` obtains its reclassifier as a reducible type at one level
above (the predicative-tower level discipline; the Abel/Adjedj validity logical relation, arXiv:2310.06376).

`LeveledContext context contextLevels` is the validity-context structure that motive carries: choice-free
evidence that `context` is a telescope of TYPES, each typed (by the grown engine) at a universe code in its
own prefix, with `contextLevels` recording the POSITIVE level (`predLevel + 1`) at which the bound variable is
a member of its type.  It pins each context variable's reducibility level (so `var` is sound at its own
level) and keeps every level positive (so CR1 and the conv `tarskiDecode` one-up step apply — see
`allLevelsPositive`).  The binder arm of the eventual recursor extends it by `LeveledContext.cons` (the fresh
binding is a type by the binder's domain premise); the `var` arm reads the recorded level.

## Positivity / mutual-index discipline

`HasTypeDescPi` appears ONLY positively (in `bindingTyped`); the index signature mentions only
`TypingContext` and `Fin _ → Nat` (no self-reference), so this is a strictly-positive, mutual-index-rule
compliant single inductive.  `allLevelsPositive` is proved by the inductive's RECURSOR (`induction`), with the
per-position `Fin` split done by a propext-clean structure `match` (position `0` vs `k+1`) — no `cases` on a
cons-shaped index, no impossible-case discrimination.

## Zero-axiom verification

The inductive carries no axioms; `allLevelsPositive` is recursor + `Nat.succ_pos` + `Nat.lt_of_succ_lt_succ`
+ `Fin.elim0`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **A leveled valid context.**  Choice-free evidence that `context` is a telescope of types (each typed at a
universe code in its prefix) and `contextLevels` assigns each entry the positive level `predLevel + 1` at which
the bound variable inhabits its type.  The validity-context the term-FT recursor's motive carries (pins each
variable's reducibility level; keeps levels positive). -/
inductive LeveledContext (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → (Fin scope → Nat) → Prop where
  | empty :
      LeveledContext profile (TypingContext.empty : TypingContext profile 0)
        (fun emptyIndex => emptyIndex.elim0)
  | cons {scope : Nat} {context : TypingContext profile scope} {contextLevels : Fin scope → Nat}
      {bindingType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
      (predLevel : Nat)
      (rest : LeveledContext profile context contextLevels)
      (bindingTyped :
        HasTypeDescPi profile context bindingType (universeCodeCell levelExpr flag)) :
      LeveledContext profile (context.cons bindingType)
        (levelCons (predLevel + 1) contextLevels)

/-- **Every entry of a leveled context sits at a positive level.**  By the leveled-context recursor: `empty`
is vacuous; `cons` deposits the head at `predLevel + 1 > 0` (`levelCons`'s position-0 branch) and recurses
into the tail at position `k+1`.  The positivity invariant the term-FT recursor relies on throughout (CR1 and
the conv `tarskiDecode` one-up step both require positive levels). -/
theorem LeveledContext.allLevelsPositive {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {contextLevels : Fin scope → Nat}
    (leveled : LeveledContext profile context contextLevels) :
    ∀ index : Fin scope, 0 < contextLevels index := by
  induction leveled with
  | empty => exact fun index => index.elim0
  | cons predLevel _rest _bindingTyped tailPositive =>
      intro index
      match index with
      | ⟨0, _⟩ => exact Nat.succ_pos predLevel
      | ⟨position + 1, isLtSucc⟩ =>
          exact tailPositive ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

end FX1Poly.Typed
