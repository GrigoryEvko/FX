import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationEmptyMember
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationNeutralMembers
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables

/-! # FX1Poly/Typed/BaseTypeFormationArm
    — the base-type formation FT ARM: dispatch a base-type rule hit to its per-code member (TYTAB-4 step 4 / FTGEN-6)

`BaseTypeFormationEmptyMember.lean` + `BaseTypeFormationNeutralMembers.lean` discharged the five per-code base-type
formation members (`Empty` via the `dataEmpty` arm; `Bool` / `Nat` / `Unit` / `Interval` via the `neutral` arm).
This file assembles them into the base-type sub-family arm of the native `formationFundamental` premise: given that a
generator carries a base-type table row (`baseTypeRuleDescOf generator = some baseRule`), the cell
`mkGen generator payload children` is a bound-reducible member of the row's output universe under any closing
substitution.

## The dispatch

`baseTypeRuleTableHitIsNullaryBaseCode` pins the generator to one of the five nullary base codes (a clean 5-way
disjunction over the `if`-chain table — no 200-way `cases Generator`).  `baseTypeRuleTableOutputIsType0` collapses the
row's output universe to the closed `Type@0(standard)` cell up front, so every branch's classifier is uniform.  In
each branch, `subst` the generator and `cases children` (the base code's `binderShifts` is `[]`, so the only child
spine is `childNil`); the payload sits at `Unit` and unifies with `()` by structure eta, so `mkGen genXCode payload
childNil` is defeq the cell `XTypeCell`, and the matching per-code member closes the goal.

## Relation to the full `formationFundamental` premise

This arm is stated against the TABLE-HIT hypothesis `baseTypeRuleDescOf generator = some baseRule` — the substantive
content.  The native `formationFundamental` premise of `HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms`
supplies `bundle.formationRule generator = some rule`; the base-type slice (`cases rule` → `.baseType baseRule`) feeds
through the bundle's `formationRuleOf` `.baseType` inversion to `baseTypeRuleDescOf generator = some baseRule`, then
into this arm — the trivial plumbing left for the `formationFundamental` assembly brick.

## Zero-axiom verification

`congrFun` on the output-pinning lemma + a 5-way `rcases` over the table inversion + `subst`/`cases children` + the
five shipped members.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The base-type formation FT arm (TYTAB-4 step 4 / FTGEN-6).**  A generator carrying a base-type table row
(`baseTypeRuleDescOf generator = some baseRule`) makes `mkGen generator payload children` a bound-reducible member of
the row's output universe under any closing substitution, given `0 < bound`.  Dispatches the five nullary base codes
to their per-code members (`Empty` → `dataEmpty`; `Bool`/`Nat`/`Unit`/`Interval` → `neutral`).  The substantive
base-type sub-family of the native `formationFundamental` premise. -/
theorem fundamentalBaseTypeRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {baseRule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some baseRule)
    (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
      (baseRule.outputUniverse scope) := by
  have outputEq : baseRule.outputUniverse scope
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
    congrFun (baseTypeRuleTableOutputIsType0 isBaseType) scope
  rw [outputEq]
  rcases baseTypeRuleTableHitIsNullaryBaseCode isBaseType with
    isBool | isEmpty | isNat | isUnit | isInterval
  · subst isBool; cases children
    show FundamentalConclusionAtBoundedSucc env bound context (boolTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    exact fundamentalBaseTypeBoolCodeAtBoundedSucc env bound context boundPositive
  · subst isEmpty; cases children
    show FundamentalConclusionAtBoundedSucc env bound context (emptyTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    exact fundamentalBaseTypeEmptyCodeAtBoundedSucc env bound context boundPositive
  · subst isNat; cases children
    show FundamentalConclusionAtBoundedSucc env bound context (natTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    exact fundamentalBaseTypeNatCodeAtBoundedSucc env bound context boundPositive
  · subst isUnit; cases children
    show FundamentalConclusionAtBoundedSucc env bound context (unitTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    exact fundamentalBaseTypeUnitCodeAtBoundedSucc env bound context boundPositive
  · subst isInterval; cases children
    show FundamentalConclusionAtBoundedSucc env bound context (intervalTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    exact fundamentalBaseTypeIntervalCodeAtBoundedSucc env bound context boundPositive

end FX1Poly.Typed
