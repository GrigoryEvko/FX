import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DescTelescopeInversion
    — cons-shape inversion for the grown-engine premise telescope

The fundamental theorem's `genFormationPi` arm receives the children's typing as a `DescTelescopePi`
telescope; to dispatch to the shipped per-former membership rules it must recover each child's
`HasTypeDescPi` derivation.  `DescTelescopePi.consInversion` projects the head typing and the tail telescope
out of a CONS-shaped telescope (`headLevel :: restLevels` over `childCons head rest`) — the single inversion
both the `genFormationPi` arm and the formation engine's `genFormation` arm consume (after casing the
former generator to the two-child Π/Σ shape).

## Zero-axiom verification

The scrutinee's `levels` / `children` indices are fixed to the cons shapes, so `cases` resolves to the sole
`cons` constructor (the `nil` constructor's `[]` / `.childNil` indices cannot unify) — a SINGLE-arm
destructuring with no impossible-case discrimination, hence no `propext` / `Quot.sound` leak (the
indexed-partial-match trap needs a refuted arm; here the refutation is by the `List` index alone, which
`cases` discharges definitionally).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Cons-shape inversion of the grown premise telescope.**  A `DescTelescopePi` over a non-empty level
list `headLevel :: restLevels` and a `childCons head rest` child vector came through the `cons`
constructor, so it splits into the head's `HasTypeDescPi` typing (at `universeCodeCell headLevel flag`) and
the tail telescope over `restLevels` / `rest` in the binder-extended context `context.cons head`. -/
theorem DescTelescopePi.consInversion {profile : PolyProfile} {baseScope currentDepth : Nat}
    {restShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)} {headLevel : LevelExpr}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren restShifts baseScope}
    (telescope : DescTelescopePi profile context (headLevel :: restLevels) flag
      (.childCons head rest)) :
    HasTypeDescPi profile context head (universeCodeCell headLevel flag) ∧
      DescTelescopePi profile (currentDepth := currentDepth + 1)
        (context.cons head) restLevels flag rest := by
  cases telescope with
  | cons _context _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      exact ⟨headTyped, restTyped⟩

end FX1Poly.Typed
