import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.DescTelescopeReach

/-! # FX1Poly/Typed/FlatDescTelescope
    — the FLAT (non-cumulative) formation premise telescope: the substrate for the non-dependent data formers

`DescTelescopeReach` proved that the formation engine's premise telescope (`DescTelescope`) forces its
children's binderShifts to be the CUMULATIVE sequence `[0, 1, 2, ...]` — each child one binder deeper than the
last.  So the non-dependent two-child type-code formers `product` / `sum` / `either` / `arrow` / `equiv`, whose
binderShifts are `[0, 0]` (both children at the SAME base scope), are structurally UNREACHABLE by `genFormation`
(`DescTelescope.noFlatTwoChildTelescope`).  Typing them needs a different premise shape: a FLAT telescope where
every sibling child is a type under the SAME base context, with no binder extension.

This file builds that flat telescope as a STANDALONE inductive `FlatDescTelescope` — it merely REFERENCES the
already-defined `HasTypeDesc` in its `cons` premise (it is NOT mutual with it), so ordinary `induction` works on
it directly (unlike `DescTelescope`, which needs term-mode `match`-recursion).  It is the row-independent
substrate (the first green increment of the flat-formation track, #934) that a future flat `genFormation` arm
will consume to type the non-dependent data formers; this file does NOT yet add that engine arm — it builds and
validates the premise shape and demonstrates it represents exactly the `[0, 0]` shape `DescTelescope` cannot.

## The representability gap, closed

`productTypeZeroFlatPremise` witnesses that the concrete `[0, 0]` children of `product (Type@0) (Type@0)` DO
form a `FlatDescTelescope`, and `productChildrenFlatButNotCumulative` bundles that with
`DescTelescope.noFlatTwoChildTelescope` into the precise "strictly more expressive on the flat shape" statement:
the same children have a flat telescope but provably no cumulative (`DescTelescope`) telescope.  So
`FlatDescTelescope` is the right premise for the non-dependent formers, and the engine generalization is the
only remaining piece.

## Zero-axiom verification

`binderShiftsAreAllZero` is a direct `induction` over the standalone (non-mutual) inductive — `nil` is `rfl`,
`cons` rewrites by `List.length_cons` / `List.replicate_succ` and the hypothesis.  `twoChildComponents` is the
single-live-`cons`-then-`nil` projection (no impossible-case discrimination → no `propext` / `Quot.sound` leak,
exactly as the `DescTelescope` projections).  The witnesses are direct constructor applications and the
shipped `universeFormation`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A FLAT formation premise telescope: every child is a type at its own universe level under the SAME base
`context` (no binder extension between siblings), so all children sit at de Bruijn shift 0.  Standalone
inductive referencing the already-defined `HasTypeDesc` (NOT mutual with it), so `induction` applies directly.
The non-dependent counterpart of `DescTelescope`, whose `cons` extends the context (`context.cons head`) and so
forces the cumulative shift shape. -/
inductive FlatDescTelescope (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    {binderShifts : List Nat} → List LevelExpr → RawTermChildren binderShifts scope → Prop where
  | nil : FlatDescTelescope profile context flag [] .childNil
  | cons {restShifts : List Nat} (head : RawTerm (scope + 0)) (headLevel : LevelExpr)
      (restLevels : List LevelExpr) (rest : RawTermChildren restShifts scope)
      (headTyped : HasTypeDesc profile context head (universeCodeCell headLevel flag))
      (restTyped : FlatDescTelescope profile context flag restLevels rest) :
      FlatDescTelescope profile context flag (headLevel :: restLevels) (.childCons head rest)

/-- **A flat telescope forces ALL-ZERO binderShifts.**  The flat analogue of
`DescTelescope.binderShiftsAreCumulative`: a flat telescope of `n` children has binderShifts `[0, 0, ..., 0]`
(`List.replicate n 0`), because every `cons` keeps the same base context and so records shift 0.  Direct
`induction` (the inductive is standalone, not mutual). -/
theorem FlatDescTelescope.binderShiftsAreAllZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    binderShifts = List.replicate levels.length 0 := by
  induction telescope with
  | nil => rfl
  | cons _head _headLevel restLevels _rest _headTyped _restTyped restHypothesis =>
      rw [List.length_cons, List.replicate_succ, restHypothesis]

/-- **Two-child projection.**  A flat telescope over the two-child `[0, 0]` spine yields BOTH children typed
under the SAME base context — the non-dependent former shape (first a type, second a type, neither binding the
other).  The flat counterpart of `DescTelescope.twoChildComponents` (which types the codomain under
`context.cons child0`).  Single live `cons` then `nil`, the `[0, 0]` spine refuting the other arms by index
alone — no `propext` / `Quot.sound`. -/
theorem FlatDescTelescope.twoChildComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {levels : List LevelExpr}
    {children : RawTermChildren [0, 0] scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∃ (firstChild secondChild : RawTerm scope) (firstLevel secondLevel : LevelExpr),
      levels = [firstLevel, secondLevel] ∧
      HasTypeDesc profile context firstChild (universeCodeCell firstLevel flag) ∧
      HasTypeDesc profile context secondChild (universeCodeCell secondLevel flag) := by
  cases telescope with
  | cons firstChild firstLevel _restLevels _rest firstTyped restTelescope =>
      cases restTelescope with
      | cons secondChild secondLevel _restLevels2 _rest2 secondTyped tailTelescope =>
          cases tailTelescope with
          | nil => exact ⟨firstChild, secondChild, firstLevel, secondLevel, rfl, firstTyped, secondTyped⟩

/-- The `[0, 0]` children of `product (Type@0) (Type@0)`: both children are the universe code `Type@0`. -/
def flatProductTypeZeroChildren (flag : UniverseFlag) : RawTermChildren [0, 0] 0 :=
  .childCons (universeCodeCell LevelExpr.lzero flag)
    (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil)

/-- **The `product (Type@0) (Type@0)` children form a flat telescope.**  Each `Type@0`
(`universeCodeCell lzero`) is typed at `Type@1` (`universeCodeCell lzero.lsucc`) by `HasTypeDesc.universeFormation`
under the empty context — exactly the flat premise the non-dependent `product` former needs. -/
theorem productTypeZeroFlatPremise (profile : PolyProfile) (flag : UniverseFlag) :
    FlatDescTelescope profile TypingContext.empty flag
      [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] (flatProductTypeZeroChildren flag) :=
  FlatDescTelescope.cons (universeCodeCell LevelExpr.lzero flag) LevelExpr.lzero.lsucc
    [LevelExpr.lzero.lsucc] (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil)
    (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
    (FlatDescTelescope.cons (universeCodeCell LevelExpr.lzero flag) LevelExpr.lzero.lsucc []
      .childNil
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
      (FlatDescTelescope.nil))

/-- **The flat telescope is strictly more expressive on the `[0, 0]` shape.**  The `product (Type@0) (Type@0)`
children HAVE a flat telescope (`productTypeZeroFlatPremise`) but provably have NO cumulative `DescTelescope`
(`DescTelescope.noFlatTwoChildTelescope`, `DescTelescopeReach`).  This is the precise statement of why the
non-dependent data formers need the flat premise: `FlatDescTelescope` represents exactly what `DescTelescope`
structurally cannot. -/
theorem productChildrenFlatButNotCumulative (profile : PolyProfile) (flag : UniverseFlag) :
    FlatDescTelescope profile TypingContext.empty flag
        [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] (flatProductTypeZeroChildren flag) ∧
      ¬ ∃ levels, DescTelescope profile (currentDepth := 0) TypingContext.empty levels flag
          (flatProductTypeZeroChildren flag) :=
  ⟨productTypeZeroFlatPremise profile flag,
    fun ⟨_levels, cumulativeTelescope⟩ =>
      DescTelescope.noFlatTwoChildTelescope cumulativeTelescope⟩

end FX1Poly.Typed
