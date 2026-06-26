import FX1Poly.Tier0.Type.Level.LevelExpr

/-! # FX1Poly/Tier0/Type/Level/LevelExprTower — the n-fold-`lsucc` tower ℕ ↪ LevelExpr

The standalone level-algebra fact the predicative universe tower rests on: the family
`universeLevelOfNat : ℕ → LevelExpr` (`Type@n`'s level, `n`-fold `lsucc` over `lzero`) injects ℕ into the
level expressions.  This is term-INDEPENDENT — it lives purely in the Tier0 level algebra (`LevelExpr`,
`Init` only), with no `RawTerm` / typing / reducibility dependency — so it is the foundation the Typed
universe tower (`universeLevelTower`, `universeHierarchy_isInfiniteNonCollapsingTower`) and the no-top
metatheory (`universeHierarchyHasNoTop`) DELEGATE to, rather than a fact those `RawTerm`-level files own.

## Zero-axiom verification

`universeLevelOfNat_injective` is a clean `induction … generalizing` with `cases` on the cross-constructor
`lzero`/`lsucc` contradictions (no-confusion, propext-free — the idiom of `LevelExpr.ne_lsucc_self`) and
`injection` + `congrArg Nat.succ` on the matching case.  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Universe

/-- The level expression `Type@n`: `n`-fold `lsucc` over `lzero`.  Structural recursion on the `Nat`, so
`universeLevelOfNat (n+1)` reduces definitionally to `LevelExpr.lsucc (universeLevelOfNat n)`. -/
def universeLevelOfNat : Nat → LevelExpr
  | 0 => LevelExpr.lzero
  | (k + 1) => LevelExpr.lsucc (universeLevelOfNat k)

/-- The n-fold-`lsucc` family injects ℕ into the level algebra: distinct natural numbers name distinct levels.
By `induction … generalizing`: the cross-constructor `lzero`-vs-`lsucc` cases close by `cases` (no-confusion,
propext-free), and the `lsucc`-vs-`lsucc` case strips one successor by `injection` and recurses.  This is the
level-side injectivity that makes the universe tower non-collapsing. -/
theorem universeLevelOfNat_injective {m n : Nat}
    (sameLevels : universeLevelOfNat m = universeLevelOfNat n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ priorRight => cases sameLevels
  | succ priorLeft inductiveHypothesis =>
      cases n with
      | zero => cases sameLevels
      | succ priorRight =>
          injection sameLevels with innerLevelsEq
          exact congrArg Nat.succ (inductiveHypothesis innerLevelsEq)

end FX1Poly.Universe
