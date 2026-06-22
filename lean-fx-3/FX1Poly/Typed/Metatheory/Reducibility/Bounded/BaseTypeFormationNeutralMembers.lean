import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedFormationArityDispatch
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves
import FX1Poly.Core.Rewriting.Normalize.RawTermNF
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStep

/-! # FX1Poly/Typed/BaseTypeFormationNeutralMembers
    — the three NEUTRAL base-code formation FT members + the bool flat-data member (TYTAB-4 step 4 / FTGEN-6)

Companion to `BaseTypeFormationEmptyMember.lean`.  That file discharged the base-type arm's `gen_emptyCode` case
via the dedicated `ReducibleTypeStepBounded.dataEmpty` arm (the empty type pins to `emptyTaitCandidate`).  This file
discharges the OTHER four base-type rows — `gen_natCode` / `gen_unitCode` / `gen_intervalCode` via the `neutral`
arm, and `gen_boolCode` via the `dataFlat` arm (it is now a canonical data code) — all classified at `Type@0`.
Together the five complete the per-code base-type formation members; the dispatching `formationFundamental`
base-type arm (the next brick) routes each base generator to its member.

## Why Nat / Unit / Interval use the `neutral` arm (and Bool the `dataFlat` arm)

`emptyTypeCell` has a bespoke reducibility arm; `Nat`/`Unit`/`Interval` do not, and are NOT flat data codes
(`Generator.isFlatDataCode` is `true` for `product`/`sum`/`either`/`arrow`/`equiv`/`bool`), so the `dataFlat` arm
does not apply to them.  `Bool` IS now a flat data code (DEP-MODEL), so it takes the `dataFlat` arm instead — see
`fundamentalFlatDataBaseCodeAtBoundedSucc` below.  Each of the three remaining is a closed nullary type-former LEAF
— `mkGen gen_XCode () childNil`, childless, non-redex head — so it is `isStepNormalForm` by `rfl` and reducible AS A
TYPE via the `neutral` arm with the SN Tait candidate `IsStronglyNormalizing`.  The `neutral` arm's five gates are
all discharged by computation:

  * `noWeakHeadStep` — the cell takes no `Step` (`isStepNormalForm_blocks_step` on the `rfl` normality), hence no
    `WeakHeadStep` (`WeakHeadStep.toStep`);
  * `rootGenerator ≠ gen_piTyCode` / `≠ gen_universeCode` / `≠ gen_emptyCode` — distinct enum constructors, refuted
    by `nomatch` once `(mkGen gen_XCode ()  childNil).rootGenerator` reduces to `gen_XCode`;
  * `isFlatDataCode = false` — `rfl`.

Despite its historical name, the `neutral` arm requires NO `IsNeutral` witness (that predicate is for elimination
spines); the three type codes are canonical formers, and the arm fires on the generator-discrimination gates alone.
SN of the cell (the `universeMembershipIntroAtBounded` `typeCodeSN` slot) is the same `rfl`-normality fed through
`isStronglyNormalizing_of_noStep`.  The output level `lzero` denotes `0 < bound` from `boundPositive` — the full
arm reads `boundPositive` off the formation level gate (`0 ≤ denote level env < bound`).

## The generic helper

All four cases differ only in which scope-polymorphic cell family `cellAt : {s} → RawTerm s` they instantiate, so
the substantive work lives once in `fundamentalNeutralBaseCodeAtBoundedSucc`, parameterized by the family plus its
substitution-inertness, leaf-normality, and the three generator discriminations — each supplied by `rfl`/`nomatch`
at the concrete instance.  `Nat` / `Unit` / `Interval` are thin instantiations of this neutral helper; `Bool`
instantiates the `dataFlat` helper (`fundamentalFlatDataBaseCodeAtBoundedSucc`) at `@boolTypeCell`.

## Zero-axiom verification

`subst` rewrites + `universeMembershipIntroAtBounded` + the `neutral` reducibility arm + `noStep`-SN, with the
instance gates closed by `rfl` / `nomatch`.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Generic neutral base-code formation FT member (TYTAB-4 step 4 / FTGEN-6).**  For any scope-polymorphic nullary
type-former family `cellAt` that is substitution-inert, a step-normal leaf, and whose root generator is none of
`gen_piTyCode` / `gen_universeCode` / `gen_emptyCode` and is not a flat data code, the cell is a bound-reducible
member of `Type@0` under any closing substitution (given `0 < bound`).  The `FundamentalConclusionAtBoundedSucc`
formation obligation, discharged through the `neutral` reducibility arm with the SN Tait candidate.  Instantiated
below at `Nat` / `Unit` / `Interval` (`Bool` uses the `dataFlat` helper). -/
theorem fundamentalNeutralBaseCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    (cellAt : {s : Nat} → RawTerm s)
    (boundPositive : 0 < bound)
    (substInert : ∀ (targetScope : Nat) (substitution : RawTermSubst scope (targetScope + 1)),
      RawTerm.subst substitution (@cellAt scope) = @cellAt (targetScope + 1))
    (normalAt : ∀ (s : Nat), RawTerm.isStepNormalForm (@cellAt s))
    (notPi : ∀ (s : Nat), (@cellAt s).rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : ∀ (s : Nat), (@cellAt s).rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : ∀ (s : Nat), (@cellAt s).rootGenerator ≠ Generator.gen_emptyCode)
    (notFlat : ∀ (s : Nat), (@cellAt s).rootGenerator.isFlatDataCode = false) :
    FundamentalConclusionAtBoundedSucc env bound context (@cellAt scope)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := by
  intro targetScope substitution _envReducible
  rw [subst_universeCodeCell, substInert targetScope substitution]
  refine universeMembershipIntroAtBounded env LevelExpr.lzero UniverseFlag.standard bound _
    boundPositive ?cellStronglyNormalizing ?cellReducibleAsType
  · exact StepStar.isStronglyNormalizing_of_noStep
      (fun target step => RawTerm.isStepNormalForm_blocks_step (normalAt (targetScope + 1)) target step)
  · exact ⟨IsStronglyNormalizing, ReducibleTypeStepBounded.neutral
      (fun reduct weakHeadStep =>
        RawTerm.isStepNormalForm_blocks_step (normalAt (targetScope + 1)) reduct weakHeadStep.toStep)
      (notPi (targetScope + 1)) (notUniverse (targetScope + 1)) (notEmpty (targetScope + 1))
      (notFlat (targetScope + 1))⟩

/-- **Generic FLAT-DATA base-code formation FT member.**  The `dataFlat` counterpart of
`fundamentalNeutralBaseCodeAtBoundedSucc`: for a scope-polymorphic nullary type-former family `cellAt` that is
substitution-inert, a step-normal leaf, whose root is a canonical data code (`isFlatDataCode = true`) and not
carrier-aware (`carrierCombinator? = none`), the cell is a bound-reducible member of `Type@0` — its
reducibility-as-type being the canonical-forms candidate `dataTaitCandidate (flatCodeValuePredicate root)` via the
`dataFlat` arm, NOT the SN `neutral` candidate.  This is the candidate a dependent eliminator over the data type
consumes (it decomposes a scrutinee member into value-or-neutral).  Instantiated below at `Bool`; reused for any
future nullary data code pinned to its canonical candidate. -/
theorem fundamentalFlatDataBaseCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    (cellAt : {s : Nat} → RawTerm s)
    (boundPositive : 0 < bound)
    (substInert : ∀ (targetScope : Nat) (substitution : RawTermSubst scope (targetScope + 1)),
      RawTerm.subst substitution (@cellAt scope) = @cellAt (targetScope + 1))
    (normalAt : ∀ (s : Nat), RawTerm.isStepNormalForm (@cellAt s))
    (flatPinned : ∀ (s : Nat), (@cellAt s).rootGenerator.isFlatDataCode = true)
    (notCarrierAware : ∀ (s : Nat), (@cellAt s).rootGenerator.carrierCombinator? = none) :
    FundamentalConclusionAtBoundedSucc env bound context (@cellAt scope)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := by
  intro targetScope substitution _envReducible
  rw [subst_universeCodeCell, substInert targetScope substitution]
  refine universeMembershipIntroAtBounded env LevelExpr.lzero UniverseFlag.standard bound _
    boundPositive ?cellStronglyNormalizing ?cellReducibleAsType
  · exact StepStar.isStronglyNormalizing_of_noStep
      (fun target step => RawTerm.isStepNormalForm_blocks_step (normalAt (targetScope + 1)) target step)
  · exact ⟨_, ReducibleTypeStepBounded.dataFlat (flatPinned (targetScope + 1))
      (notCarrierAware (targetScope + 1))⟩

/-- The `gen_boolCode` base-type formation FT member: `Bool` is a bound-reducible member of `Type@0`, its
reducibility-as-type pinned to the canonical-forms candidate `dataTaitCandidate boolIsValue` via `dataFlat`. -/
theorem fundamentalBaseTypeBoolCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (boolTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  fundamentalFlatDataBaseCodeAtBoundedSucc env bound context (@boolTypeCell) boundPositive
    (fun _targetScope _substitution => rfl) (fun _s => rfl) (fun _s => rfl) (fun _s => rfl)

/-- The `gen_natCode` base-type formation FT member: `Nat` is a bound-reducible member of `Type@0`, its
reducibility-as-type pinned to the canonical-forms candidate `dataTaitCandidate IsNatStructured` via `dataFlat`
(DEP-NAT-MODEL — nat joined `isFlatDataCode`, so it rides the data arm like `Bool`, not the SN `neutral` arm). -/
theorem fundamentalBaseTypeNatCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (natTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  fundamentalFlatDataBaseCodeAtBoundedSucc env bound context (@natTypeCell) boundPositive
    (fun _targetScope _substitution => rfl) (fun _s => rfl) (fun _s => rfl) (fun _s => rfl)

/-- The `gen_unitCode` base-type formation FT member: `Unit` is a bound-reducible member of `Type@0`. -/
theorem fundamentalBaseTypeUnitCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (unitTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  fundamentalNeutralBaseCodeAtBoundedSucc env bound context (@unitTypeCell) boundPositive
    (fun _targetScope _substitution => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

/-- The `gen_intervalCode` base-type formation FT member: `Interval` is a bound-reducible member of `Type@0`. -/
theorem fundamentalBaseTypeIntervalCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (intervalTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  fundamentalNeutralBaseCodeAtBoundedSucc env bound context (@intervalTypeCell) boundPositive
    (fun _targetScope _substitution => rfl) (fun _s => rfl)
    (fun _s rootEquation => nomatch rootEquation) (fun _s rootEquation => nomatch rootEquation)
    (fun _s rootEquation => nomatch rootEquation) (fun _s => rfl)

end FX1Poly.Typed
