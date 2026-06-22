import FX1Poly.Typed.Metatheory.Reducibility.Bounded.NullaryIntroRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.SNNeutralIntroRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CarrierAwareIntroRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BinderIntroRows

/-! # FX1Poly/Typed/UnionIntroFundamental
    — the native `introFundamental` premise discharged at the intro table (TYTAB-4 step 4)

`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` (`BoundedUnionFundamental.lean`) takes three explicit
table-arm FT premises; this file discharges the SECOND — the `introFundamental` premise — for ANY generator
whose intro rule comes from `introRuleOf` (the `fxTypingBundle.intro` table).

## The seventeen-row `introRuleOf_cases` assembly

`introRuleOf` tags every introducer generator with one of seventeen `IntroRule` rows, grouped into four
families, each shipped as a per-row bounded-member FT theorem:

  * the six NULLARY data constructors (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` /
    `natZero`) → `fundamental<X>IntroRowAtBoundedSucc` (no obligation premise — childless leaves);
  * the six SN-NEUTRAL recursive/structural constructors (`natSucc` / `refl` / `listCons` / `optionSome` /
    `listNil` / `optionNone`) → the `SNNeutralIntroRows` rows (output type takes the `neutral` arm, candidate
    `IsStronglyNormalizing`);
  * the three CARRIER-AWARE flat constructors (`pair` / `eitherInl` / `eitherInr`) → the
    `CarrierAwareIntroRows` rows (output type takes the content-bearing `dataFlatCarrierAware` arm);
  * the two GRADED BINDERS (`lam` / `pathLam`) → the `BinderIntroRows` rows (`lam` via the dependent-arrow
    binder engine, `pathLam` via the open-body SN reflection).

`introRuleOf_cases` reverse-extracts the seventeen-way `(generator = gen_X ∧ rule = XIntroRule)` disjunction;
each arm substitutes the pinned `XIntroRule` (so the glue's `memberCell` / `outputType` goal and obligation
premise reduce to the per-row theorem's by construction) and feeds the matching row.  The graded binders'
`sideHolds` (a `gradedBinderChecks` usage discipline) is not consumed — the reducible-member witness is
independent of the usage grade.

This is the native (table-driven) analogue of the grown intro arms — assembled from per-row table theorems
rather than a per-family inductive, so a future introducer row (a `ProfileExtension` constructor) adds one
disjunct here with no change to the existing arms.

## Zero-axiom verification

`rcases introRuleOf_cases` (17 arms) feeding the per-row theorems (themselves zero-axiom).  No new members,
no induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The native `introFundamental` premise (TYTAB-4 step 4).**  Every generator carrying an `introRuleOf`
intro rule makes its introduced member cell a bound-reducible member of the rule's output type, given the side
condition and the obligation IHs.  The seventeen-row `introRuleOf_cases` assembly: each arm substitutes the
pinned `IntroRule` and feeds the shipped per-row theorem, whose obligation premise / output match the glue's by
construction.  Discharges the `introFundamental` argument of
`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` for any `fxTypingBundle`-style intro table. -/
theorem fundamentalIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : IntroRule}
    {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (isIntro : introRuleOf generator = some rule)
    (_sideHolds : rule.sideCondition scope args)
    (premisesFundamental : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
      (rule.outputType scope args params) := by
  rcases introRuleOf_cases isIntro with
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact fundamentalBoolTrueIntroRowAtBoundedSucc env bound context
  · exact fundamentalBoolFalseIntroRowAtBoundedSucc env bound context
  · exact fundamentalUnitIntroRowAtBoundedSucc env bound context
  · exact fundamentalInterval0IntroRowAtBoundedSucc env bound context
  · exact fundamentalInterval1IntroRowAtBoundedSucc env bound context
  · exact fundamentalNatZeroIntroRowAtBoundedSucc env bound context
  · exact fundamentalLamIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalPathLamIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalNatSuccIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalListConsIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalOptionSomeIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalOptionNoneIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalListNilIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalEitherInlIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalEitherInrIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalPairIntroRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalReflIntroRowAtBoundedSucc env bound context premisesFundamental

end FX1Poly.Typed
