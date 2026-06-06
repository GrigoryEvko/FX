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

/-- **Cons-shape inversion of the formation premise telescope.**  A `DescTelescope` over a non-empty level
list and a `childCons` spine splits into the head's `HasTypeDesc` derivation and the tail telescope in the
binder-extended context.  This is the formation-engine analogue of `DescTelescopePi.consInversion`, used by
the formation-fragment fundamental theorem without inspecting the telescope inside a recursive call. -/
theorem DescTelescope.consInversion {profile : PolyProfile} {baseScope currentDepth : Nat}
    {restShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)} {headLevel : LevelExpr}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren restShifts baseScope}
    (telescope : DescTelescope profile context (headLevel :: restLevels) flag
      (.childCons head rest)) :
    HasTypeDesc profile context head (universeCodeCell headLevel flag) ∧
      DescTelescope profile (currentDepth := currentDepth + 1)
        (context.cons head) restLevels flag rest := by
  cases telescope with
  | cons _context _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      exact ⟨headTyped, restTyped⟩

/-- **Two-child formation telescope -> two-element level list.**  The formation-engine counterpart of
`DescTelescopePi.twoChildLevels`: a depth-0 `DescTelescope` over the concrete two-child spine
`childCons _ (childCons _ childNil)` carries exactly two universe levels.  This is the non-recursive
inversion the formation-fragment fundamental theorem's `genFormation` arm needs before dispatching to the
Π/Σ former reducibility bundle. -/
theorem DescTelescope.twoChildLevels {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levelsList : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 1] baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levelsList flag children) :
    ∃ domainLevel codomainLevel, levelsList = [domainLevel, codomainLevel] := by
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest _headTyped restTyped =>
      cases restTyped with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 _headTyped2 tailTelescope =>
          cases tailTelescope with
          | nil => exact ⟨domainLevel, codomainLevel, rfl⟩

/-- **Two-child formation telescope ⟹ both component typings.**  The TYPING companion to `twoChildLevels`
(which recovers only the levels): a depth-0 `DescTelescope` over the concrete two-child `[0,1]` spine yields
the head's typing at its universe code under `context` AND the tail head's typing under the binder-extended
`context.cons child0` — exactly the dependent former shape (domain a type, codomain a type under the domain
binder).  Composed with the generic `inversionFormerTelescopeGeneric` (GTL-08) this gives generic 2-child
former component inversion for ANY dependent binary formation former, factoring the telescope-walk half that
`inversionPiCodeComponents` / `inversionSigmaCodeComponents` each spell out by hand.  Same single-live-`cons`
discipline as `twoChildLevels` (the child spine fixes the `RawTermChildren` index; `nil` is refuted by that
index alone), so no `propext` / `Quot.sound` leak. -/
theorem DescTelescope.twoChildComponents {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 1] baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag children) :
    ∃ (child0 : RawTerm baseScope) (child1 : RawTerm (baseScope + 1))
      (domainLevel codomainLevel : LevelExpr),
      levels = [domainLevel, codomainLevel] ∧
      HasTypeDesc profile context child0 (universeCodeCell domainLevel flag) ∧
      HasTypeDesc profile (context.cons child0) child1 (universeCodeCell codomainLevel flag) := by
  cases telescope with
  | cons _context head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped tailTelescope =>
          cases tailTelescope with
          | nil => exact ⟨head, head2, domainLevel, codomainLevel, rfl, domainTyped, codomainTyped⟩

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

/-- **Two-child former telescope ⟹ two-element level list.**  A depth-0 premise telescope over the concrete
two-child spine `childCons _ (childCons _ childNil)` (the Π / Σ formers' `[0,1]` `binderShifts` shape) carries
exactly a two-element level list.  The child spine fixes the `RawTermChildren` index, so the `nil`
constructors are refuted definitionally by that index alone — a single live `cons` arm at each step, no
refuted-arm discrimination, hence no `propext` / `Quot.sound` leak (same discipline as `consInversion`).  The
`genFormationPi` fundamental-theorem arm uses it to recover `levels = [domainLevel, codomainLevel]` (needed to
state the `FormerChildrenReducible` bundle) WITHOUT casing the premise telescope as a recursion target. -/
theorem DescTelescopePi.twoChildLevels {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levelsList : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 1] baseScope}
    (telescope : DescTelescopePi profile (currentDepth := 0) context levelsList flag children) :
    ∃ domainLevel codomainLevel, levelsList = [domainLevel, codomainLevel] := by
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest _headTyped restTyped =>
      cases restTyped with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 _headTyped2 tailTelescope =>
          cases tailTelescope with
          | nil => exact ⟨domainLevel, codomainLevel, rfl⟩

/-- **One-child former telescope ⟹ one-element level list.**  The one-child (`binderShifts = [0]`) analogue of
`twoChildLevels`, for the data type-code formers (`listCode` / `optionCode`): a depth-0 premise telescope over
the concrete one-child spine `childCons _ childNil` carries exactly a one-element level list.  The child spine
fixes the `RawTermChildren [0]` index, so a single live `cons` arm then the `nil` closes it — no refuted-arm
discrimination, no `propext` / `Quot.sound` leak (same discipline as `twoChildLevels`).  Consumed by the
`genFormationPi` fundamental-theorem arm's data-former branch to recover `levels = [elementLevel]` (needed to
state the `IsReducibleMemberAt.listCodeFormationUnderSubst` conclusion) WITHOUT casing the premise telescope as
a recursion target. -/
theorem DescTelescopePi.oneChildLevel {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levelsList : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0] baseScope}
    (telescope : DescTelescopePi profile (currentDepth := 0) context levelsList flag children) :
    ∃ elementLevel, levelsList = [elementLevel] := by
  cases telescope with
  | cons _context _head elementLevel _restLevels _flag _rest _headTyped restTyped =>
      cases restTyped with
      | nil => exact ⟨elementLevel, rfl⟩

end FX1Poly.Typed
