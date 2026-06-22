import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationNeutralMembers
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/NullaryIntroRows
    — the six NULLARY data-constructor intro FT members (TYTAB-4 step 4, the intro side's leaf cases)

The value-side twin of `BaseTypeFormationNeutralMembers.lean`.  Where that file proved each neutral base
TYPE (`Bool` / `Nat` / `Unit` / `Interval`) is a bound-reducible member of `Type@0`, this file proves each
nullary VALUE constructor (`boolTrue` / `boolFalse` / `()` / `0ᵢ` / `1ᵢ` / `natZero`) is a bound-reducible
member of its base type — the six obligation-free rows of the `introFundamental` premise.

## Why one generic helper covers all six

`IsReducibleMemberAtBounded env bound typeCode term` is `∃ candidate, ReducibleTypeAtBounded env bound
typeCode candidate ∧ candidate term`.  For each nullary constructor the OUTPUT type is a neutral base type,
reducible-as-type through the `neutral` arm of `ReducibleTypeStepBounded` with the SN Tait candidate
`IsStronglyNormalizing` (exactly as `BaseTypeFormationNeutralMembers` builds it).  The value cell is a closed
nullary normal-form LEAF — childless, non-redex head — so it is `isStepNormalForm` by `rfl`, hence takes no
`Step`, hence `IsStronglyNormalizing`, hence lies in that very candidate.  So every row is the SAME witness
`⟨IsStronglyNormalizing, neutralReducible, valueSN⟩`, differing only in which type/value cell family is
instantiated.  `fundamentalNullaryIntroAtBoundedSucc` is that witness once, parameterized by the two cell
families plus their substitution-inertness, leaf-normality, and (for the type) the four `neutral`-arm
generator discriminations — each supplied by `rfl` / `nomatch` at the concrete instance.

## Zero-axiom verification

`subst` rewrites + the `neutral` reducibility arm + `noStep`-SN (both the type's `noWeakHeadStep` gate and
the value's strong normalization read off the `rfl`-normality through `isStepNormalForm_blocks_step`).  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Generic nullary data-constructor intro FT member (TYTAB-4 step 4).**  For a scope-polymorphic neutral
base type `typeCellAt` (substitution-inert, a step-normal leaf whose root generator is none of `gen_piTyCode`
/ `gen_universeCode` / `gen_emptyCode` and is not a flat data code) and a scope-polymorphic nullary value cell
`valueCellAt` (substitution-inert, a step-normal leaf), the value is a bound-reducible member of the type
under any closing substitution.  The type's reducibility candidate is `IsStronglyNormalizing` (the `neutral`
arm); the value lies in it because it is a closed normal form.  Instantiated below at the six nullary
constructors `boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` / `natZero`. -/
theorem fundamentalNullaryIntroAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    (typeCellAt valueCellAt : {s : Nat} → RawTerm s)
    (typeSubstInert : ∀ (targetScope : Nat) (substitution : RawTermSubst scope (targetScope + 1)),
      RawTerm.subst substitution (@typeCellAt scope) = @typeCellAt (targetScope + 1))
    (valueSubstInert : ∀ (targetScope : Nat) (substitution : RawTermSubst scope (targetScope + 1)),
      RawTerm.subst substitution (@valueCellAt scope) = @valueCellAt (targetScope + 1))
    (typeNormalAt : ∀ (s : Nat), RawTerm.isStepNormalForm (@typeCellAt s))
    (valueNormalAt : ∀ (s : Nat), RawTerm.isStepNormalForm (@valueCellAt s))
    (typeNotPi : ∀ (s : Nat), (@typeCellAt s).rootGenerator ≠ Generator.gen_piTyCode)
    (typeNotUniverse : ∀ (s : Nat), (@typeCellAt s).rootGenerator ≠ Generator.gen_universeCode)
    (typeNotEmpty : ∀ (s : Nat), (@typeCellAt s).rootGenerator ≠ Generator.gen_emptyCode)
    (typeNotFlat : ∀ (s : Nat), (@typeCellAt s).rootGenerator.isFlatDataCode = false) :
    FundamentalConclusionAtBoundedSucc env bound context (@valueCellAt scope) (@typeCellAt scope) := by
  intro targetScope substitution _envReducible
  rw [typeSubstInert targetScope substitution, valueSubstInert targetScope substitution]
  refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
  · exact ReducibleTypeStepBounded.neutral
      (fun reduct weakHeadStep =>
        RawTerm.isStepNormalForm_blocks_step (typeNormalAt (targetScope + 1)) reduct weakHeadStep.toStep)
      (typeNotPi (targetScope + 1)) (typeNotUniverse (targetScope + 1)) (typeNotEmpty (targetScope + 1))
      (typeNotFlat (targetScope + 1))
  · exact StepStar.isStronglyNormalizing_of_noStep
      (fun target step =>
        RawTerm.isStepNormalForm_blocks_step (valueNormalAt (targetScope + 1)) target step)

/-- The `gen_boolTrue` intro FT member: `boolTrue` is a bound-reducible member of `Bool`. -/
theorem fundamentalBoolTrueIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_boolTrue () RawTermChildren.childNil) (boolTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@boolTypeCell)
    (fun {s} => RawTerm.mkGen Generator.gen_boolTrue () RawTermChildren.childNil (scope := s))
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_boolFalse` intro FT member: `boolFalse` is a bound-reducible member of `Bool`. -/
theorem fundamentalBoolFalseIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_boolFalse () RawTermChildren.childNil) (boolTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@boolTypeCell)
    (fun {s} => RawTerm.mkGen Generator.gen_boolFalse () RawTermChildren.childNil (scope := s))
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_unit` intro FT member: `()` is a bound-reducible member of `Unit`. -/
theorem fundamentalUnitIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context (unitCell (scope := scope))
      (unitTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@unitTypeCell) (@unitCell)
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_interval0` intro FT member: `0ᵢ` is a bound-reducible member of `Interval`. -/
theorem fundamentalInterval0IntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context (intervalZeroCell (scope := scope))
      (intervalTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@intervalTypeCell) (@intervalZeroCell)
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_interval1` intro FT member: `1ᵢ` is a bound-reducible member of `Interval`. -/
theorem fundamentalInterval1IntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context (intervalOneCell (scope := scope))
      (intervalTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@intervalTypeCell) (@intervalOneCell)
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_natZero` intro FT member: `natZero` is a bound-reducible member of `Nat`. -/
theorem fundamentalNatZeroIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) :
    FundamentalConclusionAtBoundedSucc env bound context (natZeroCell (scope := scope))
      (natTypeCell (scope := scope)) :=
  fundamentalNullaryIntroAtBoundedSucc env bound context (@natTypeCell) (@natZeroCell)
    (fun _targetScope _substitution => rfl) (fun _targetScope _substitution => rfl)
    (fun _s => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

end FX1Poly.Typed
