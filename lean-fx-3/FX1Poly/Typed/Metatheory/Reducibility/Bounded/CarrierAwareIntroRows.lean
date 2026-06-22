import FX1Poly.Typed.Metatheory.Reducibility.Bounded.SNNeutralIntroRows
import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers

/-! # FX1Poly/Typed/CarrierAwareIntroRows
    — the carrier-aware data-constructor intro FT members (TYTAB-4 step 4, the intro side's content-bearing
      flat-constructor cases: product / coproduct)

The introducers whose OUTPUT type is a carrier-aware flat former (`product` / `either` — `isFlatDataCode=true`,
`carrierCombinator?=some`).  Unlike the SN-neutral introducers, these take the `dataFlatCarrierAware` reducibility
arm: the candidate is the CONTENT-BEARING `carrierAware{Pair,Either}Candidate firstCandidate secondCandidate`
(NOT `IsStronglyNormalizing` — the `neutral` arm is gated off for flat codes).  So the member witness must show
the constructed value lies in that content-bearing candidate, which is exactly the general
`carrierAware{Pair,Either}Candidate.memberOf{ReducibleComponents,ReducibleInl,ReducibleInr}` Core keystone
(SN-component data-intro).

The decisive move: the SAME component candidates threaded from the obligation IHs feed BOTH the formation arm
(`ReducibleTypeStepBounded.dataFlatCarrierAware`, which stores `combinator.assemble firstCandidate secondCandidate`)
AND the member builder — so no `ReducibleTypeAtBounded.deterministic` alignment is needed.  `pairLike.assemble =
carrierAwarePairCandidate` and `coproductLike.assemble = carrierAwareEitherCandidate` make the formation arm and
the member builder agree by defeq.

This file ships the `pair` row — both component candidates come from its two VALUE obligations
(fst : A, snd : B), so it needs no universe→type-reducibility conversion.  `eitherInl` / `eitherInr` (whose
non-injected carrier comes from a formedness premise) follow with the universe-member bridge.

## Zero-axiom verification

`stronglyNormalizing_of_memberAtBoundedSucc`'s candidate destructuring (`IsReducibleMemberAtBounded` is an
existential carrying the carrier candidate + its type-reducibility + the value's membership) + the
`dataFlatCarrierAware` constructor + the Core `memberOfReducibleComponents` + `ReducibleTypeAtBounded.isReducibilityCandidate`.
No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The `gen_pair` intro FT member: `(a, b)` is a bound-reducible member of `product(A, B)` given `a : A` and
`b : B`.  Output type `product(A, B)` takes the carrier-aware flat arm (candidate `carrierAwarePairCandidate
firstCandidate secondCandidate` from the component obligations' carriers); the pair lies in it via the Core
general Σ-introduction `memberOfReducibleComponents`, and the formation arm `dataFlatCarrierAware` stores the
matching `pairLike.assemble = carrierAwarePairCandidate` candidate — so the same threaded carriers close both. -/
theorem fundamentalPairIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren pairIntroRule.argShifts scope}
    {params : RawTermChildren pairIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ pairIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (pairIntroRule.memberCell scope args)
      (pairIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons child0 (.childCons child1 .childNil),
    .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    intro targetScope substitution envReducible
    have child0Fundamental :
        FundamentalConclusionAtBoundedSucc env bound context child0 typeParam0 :=
      premisesFundamental
        { scope := scope, context := context, subject := child0, classifier := typeParam0 }
        (List.Mem.head _)
    have child1Fundamental :
        FundamentalConclusionAtBoundedSucc env bound context child1 typeParam1 :=
      premisesFundamental
        { scope := scope, context := context, subject := child1, classifier := typeParam1 }
        (List.Mem.tail _ (List.Mem.head _))
    obtain ⟨firstCandidate, firstTypeReducible, firstMember⟩ := child0Fundamental substitution envReducible
    obtain ⟨secondCandidate, secondTypeReducible, secondMember⟩ := child1Fundamental substitution envReducible
    refine ⟨carrierAwarePairCandidate firstCandidate secondCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataFlatCarrierAware (combinator := .pairLike)
        firstTypeReducible secondTypeReducible
    · exact carrierAwarePairCandidate.memberOfReducibleComponents
        (ReducibleTypeAtBounded.isReducibilityCandidate firstTypeReducible)
        (ReducibleTypeAtBounded.isReducibilityCandidate secondTypeReducible)
        firstMember secondMember

end FX1Poly.Typed
