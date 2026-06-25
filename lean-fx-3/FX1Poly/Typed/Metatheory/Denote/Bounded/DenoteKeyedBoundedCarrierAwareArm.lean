import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedReducibility
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierModelAssembler
import FX1Poly.Core.Metatheory.Reducibility.Candidates.UnaryCarrierCombinatorTable

/-! # FX1Poly/Typed/DenoteKeyedBoundedCarrierAwareArm
    — carrier-aware flat type-reducibility from component reducibility, bound-carrying (TYTAB-4 step 4)

`piReducibleAtLevelFromComponentsBounded` (DenoteKeyedBoundedGenFormationPiArm) builds the dependent-arrow's
bound-reducible-as-type from its components.  This file is the CARRIER-AWARE flat twin: a `combinator.cell` (the
product / either / equiv code — `CarrierCombinator.pairLike` / `.coproductLike` / `.equivLike`) is bound-reducible
as a type at any `level` given BOTH carriers reducible there.  It is the `IsReducibleTypeAtBounded`-level wrapper
over the inductive arm `ReducibleTypeStepBounded.dataFlatCarrierAware` — the missing builder the bounded flat
formation FT needs.  The denote-layer twin `IsReducibleTypeAtAllDenoteLevels.ofDataFlatCarrierAware` already ships;
this is its bound-carrying counterpart, the carrier-aware peer of the content-free `flatCode_isReducibleTypeAtBounded`.

## The construction

`IsReducibleTypeAtBounded env level t` is `∃ candidate, ReducibleTypeAtBounded env level t candidate`, and
`ReducibleTypeAtBounded env level = ReducibleTypeStepBounded env (denoteBelowFamilyBounded env level) level`.  Both
component existentials therefore carry derivations at the SAME below-family `denoteBelowFamilyBounded env level`, so
`ReducibleTypeStepBounded.dataFlatCarrierAware` composes them directly — the assembled candidate is
`combinator.assemble firstCandidate secondCandidate`.

## Zero-axiom verification

Two `obtain`s + one `dataFlatCarrierAware` anonymous constructor.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Carrier-aware flat type-reducibility from component reducibility (bound-carrying).**  The
`combinator.cell firstCode secondCode` (product / either / equiv) is a bound-reducible TYPE at `level` given
`firstCode` and `secondCode` reducible there.  The carrier-aware twin of `piReducibleAtLevelFromComponentsBounded`:
one `ReducibleTypeStepBounded.dataFlatCarrierAware` constructor over the two component derivations (which share the
`denoteBelowFamilyBounded env level` below-family), the assembled candidate being `combinator.assemble`. -/
theorem carrierAwareReducibleAtLevelFromComponentsBounded {scope : Nat} (env : Nat → Nat) (level : Nat)
    (combinator : CarrierCombinator) {firstCode secondCode : RawTerm scope}
    (firstReducible : IsReducibleTypeAtBounded env level firstCode)
    (secondReducible : IsReducibleTypeAtBounded env level secondCode) :
    IsReducibleTypeAtBounded env level (combinator.cell firstCode secondCode) := by
  obtain ⟨firstCandidate, firstStep⟩ := firstReducible
  obtain ⟨secondCandidate, secondStep⟩ := secondReducible
  exact ⟨combinator.assembleModel firstCandidate secondCandidate,
    ReducibleTypeStepBounded.dataFlatCarrierAware firstStep secondStep⟩

/-- **Unary carrier-aware flat type-reducibility from element reducibility (bound-carrying).**  The
`combinator.cell elementCode` (the option / list code — `UnaryCarrierCombinator.optionLike` / `.listLike`) is a
bound-reducible TYPE at `level` given `elementCode` reducible there.  The single-carrier twin of
`carrierAwareReducibleAtLevelFromComponentsBounded`: one `ReducibleTypeStepBounded.dataUnaryCarrierAware`
constructor over the element derivation, the assembled candidate being `combinator.assembleModel` (the reach-aware
model candidate).  This is the builder the option/list bounded formation FT needs to route off the content-free
`flatCode_isReducibleTypeAtBounded` (whose `unaryCarrierCombinator? = none` gate the option/list cells fail). -/
theorem unaryCarrierReducibleAtLevelFromElementBounded {scope : Nat} (env : Nat → Nat) (level : Nat)
    (combinator : UnaryCarrierCombinator) {elementCode : RawTerm scope}
    (elementReducible : IsReducibleTypeAtBounded env level elementCode) :
    IsReducibleTypeAtBounded env level (combinator.cell elementCode) := by
  obtain ⟨elementCandidate, elementStep⟩ := elementReducible
  exact ⟨combinator.assembleModel elementCandidate,
    ReducibleTypeStepBounded.dataUnaryCarrierAware elementStep⟩

end FX1Poly.Typed
