import FX1Poly.Typed.UniverseDomainMemberExtension

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsLeaves
    — the non-Π type leaves are reducible at ALL levels unconditionally (discharging cons-arm irrelevance)

`UniverseDomainMemberExtension` reduced the formation-FT cons-arm's universe-domain case to type-level
positive level-irrelevance (`IsReducibleTypeAt predLevel A → IsReducibleTypeAtAllLevels A`).  That lift is
the open obstruction ONLY at the Π-headed argument (the codomain reducibility is quantified over the
level-dependent domain candidate — `ReducibleTypeStep.existsCongr`'s degenerate-base wall).  For EVERY OTHER
type shape the lift is not merely available, it is UNCONDITIONAL — the type is reducible at every level with
no hypothesis at all:

  * `IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse` — a weak-head-normal type code that is
    neither Π- nor universe-rooted (a variable / stuck eliminator [neutral] or any DATA former — Σ / Nat /
    List / Option / Either / Id / product / sum codes) is reducible at every level with candidate
    `IsStronglyNormalizing`, via `ReducibleTypeAt.reducibleOfWeakHeadNormalFormer` at each level (the Tarski
    model classifies every data type by strong normalization — no per-former candidate).
  * `IsReducibleTypeAtAllLevels.ofUniverseCode` — a universe code `Type@e` is reducible at every level via
    `IsReducibleTypeAt.universeCode` (the universe is reducibility-sound at every fuel, each level with its
    own — different but existent — candidate, which is all `IsReducibleTypeAtAllLevels` asks).

Plugging these into the `ofUniverseMemberUnderTypeLevelIrrelevance` reduction discharges the cons-arm
universe-domain member-extension for every argument type whose code is non-Π: the type-polymorphic binder
`Π (A : Type@e). …` closes for ALL instantiations except a Π-TYPE argument (e.g. instantiating `A` with
`Nat → Nat`).  That residual Π-argument case is the sole remaining cons-arm obstruction, now sharply
isolated.

## Zero-axiom verification

Each all-levels lemma is a `fun level => …` over a shipped per-level producer
(`reducibleOfWeakHeadNormalFormer` / `IsReducibleTypeAt.universeCode`); the corollaries compose with the
reduction.  No induction, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **A weak-head-normal non-Π non-universe type code is reducible at EVERY level, unconditionally.**  The
candidate is `IsStronglyNormalizing` at each level (the Tarski model's classification of every neutral /
data-former type); `IsReducibleTypeAtAllLevels` asks only for an existent candidate per level, supplied by
`ReducibleTypeAt.reducibleOfWeakHeadNormalFormer`. -/
theorem IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse {scope : Nat}
    {typeCode : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleTypeAtAllLevels typeCode :=
  fun level =>
    ReducibleTypeAt.reducibleOfWeakHeadNormalFormer (level := level)
      weakHeadNormal notPiType notUniverse

/-- **A universe code is reducible at EVERY level, unconditionally.**  Each level supplies its own (different
but existent) universe candidate via `IsReducibleTypeAt.universeCode`. -/
theorem IsReducibleTypeAtAllLevels.ofUniverseCode {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} :
    IsReducibleTypeAtAllLevels (universeCodeCell levelExpr flag : RawTerm scope) :=
  fun level => IsReducibleTypeAt.universeCode level levelExpr flag

/-- **Cons-arm universe-domain member-extension for a non-Π non-universe argument type.**  When the argument
type code is weak-head-normal and neither Π- nor universe-rooted, its all-level reducibility is
unconditional, so the type-level-irrelevance hypothesis of `ofUniverseMemberUnderTypeLevelIrrelevance` is
discharged and the universe-domain member-extension holds: the type-polymorphic binder closes when
instantiated by a neutral or data-former type. -/
theorem IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberNonPiNonUniverseArgument {scope : Nat}
    {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode :=
  IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
    (fun _typeReducible =>
      IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse weakHeadNormal notPiType notUniverse)
    member

/-- **Cons-arm universe-domain member-extension for a universe-code argument type.**  Instantiating the
type-polymorphic binder by a universe `Type@argLevelExpr` closes: the argument's all-level reducibility is
unconditional (`ofUniverseCode`). -/
theorem IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUniverseCodeArgument {scope : Nat}
    {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {argLevelExpr : LevelExpr} {argFlag : UniverseFlag}
    (member : IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell levelExpr flag : RawTerm scope) (universeCodeCell argLevelExpr argFlag)) :
    IsReducibleMemberAtAllPositiveLevels
      (universeCodeCell levelExpr flag : RawTerm scope) (universeCodeCell argLevelExpr argFlag) :=
  IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
    (fun _typeReducible => IsReducibleTypeAtAllLevels.ofUniverseCode)
    member

end FX1Poly.Typed
