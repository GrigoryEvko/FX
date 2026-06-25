import FX1Poly.Typed.Metatheory.Reducibility.Bounded.SNNeutralIntroRows
import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedProjectionCarrierObligations

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
    refine ⟨projectionPairCandidate firstCandidate secondCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataFlatCarrierAware (combinator := .pairLike)
        firstTypeReducible secondTypeReducible
    · exact projectionPairCandidate_memberOfReducibleComponents
        (boundedTypeCarrierObligations firstTypeReducible)
        (boundedTypeCarrierObligations secondTypeReducible)
        firstMember secondMember

/-- The `gen_eitherInl` intro FT member: `inl(a)` is a bound-reducible member of `either(A, B)` given `a : A`
(LEFT) and a formedness premise on the free RIGHT `B`.  The LEFT carrier candidate comes from the value
obligation; the RIGHT carrier from the formedness obligation via the universe-member bridge
(`reducibleTypeAtBoundFromUniverseMemberBounded`, its `belowBound` read off the universe code's reducibility).
The cell lies in `reachAwareEitherCandidate` via the Core `reachAwareEitherCandidate.memberOfReducibleInl`, which
needs only the LEFT carrier's reducibility-candidate (the inl reach clause is built forward, the inr clause
vacuously); the formation arm `dataFlatCarrierAware` stores the matching `coproductLike.assembleModel =
reachAwareEitherCandidate`. -/
theorem fundamentalEitherInlIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren eitherInlIntroRule.argShifts scope}
    {params : RawTermChildren eitherInlIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ eitherInlIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (eitherInlIntroRule.memberCell scope args)
      (eitherInlIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    intro targetScope substitution envReducible
    have valueFundamental :
        FundamentalConclusionAtBoundedSucc env bound context value typeParam0 :=
      premisesFundamental
        { scope := scope, context := context, subject := value, classifier := typeParam0 }
        (List.Mem.head _)
    have rightFormednessFundamental :
        FundamentalConclusionAtBoundedSucc env bound context typeParam1
          (universeCodeCell level0 flag) :=
      premisesFundamental
        { scope := scope, context := context, subject := typeParam1,
          classifier := universeCodeCell level0 flag }
        (List.Mem.tail _ (List.Mem.head _))
    obtain ⟨firstCandidate, firstTypeReducible, firstMember⟩ := valueFundamental substitution envReducible
    have rightMember :
        IsReducibleMemberAtBounded env bound (universeCodeCell level0 flag)
          (RawTerm.subst substitution typeParam1) :=
      rightFormednessFundamental substitution envReducible
    have belowBound : LevelExpr.denote level0 env < bound := by
      obtain ⟨_, rightUniverseReducible, _⟩ := rightMember
      exact universeCodeReducibleAtBounded_belowBound rightUniverseReducible
    obtain ⟨secondCandidate, secondTypeReducible⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound rightMember belowBound
    refine ⟨reachAwareEitherCandidate firstCandidate secondCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataFlatCarrierAware (combinator := .coproductLike)
        firstTypeReducible secondTypeReducible
    · exact reachAwareEitherCandidate.memberOfReducibleInl
        (ReducibleTypeAtBounded.isReducibilityCandidate firstTypeReducible) firstMember

/-- The `gen_eitherInr` intro FT member: `inr(b)` is a bound-reducible member of `either(A, B)` given `b : B`
(the injected RIGHT carrier, `typeParam0`) and a formedness premise on the free LEFT `A` (`typeParam1`).  The
RIGHT carrier candidate comes from the value obligation; the LEFT from the formedness obligation via the
universe-member bridge.  Output `either(A, B)` puts the free LEFT first (`eitherTypeCell typeParam1 typeParam0`);
the cell lies in `reachAwareEitherCandidate` via the Core `reachAwareEitherCandidate.memberOfReducibleInr`, which
needs only the RIGHT carrier's reducibility-candidate. -/
theorem fundamentalEitherInrIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren eitherInrIntroRule.argShifts scope}
    {params : RawTermChildren eitherInrIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ eitherInrIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (eitherInrIntroRule.memberCell scope args)
      (eitherInrIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
    intro targetScope substitution envReducible
    have valueFundamental :
        FundamentalConclusionAtBoundedSucc env bound context value typeParam0 :=
      premisesFundamental
        { scope := scope, context := context, subject := value, classifier := typeParam0 }
        (List.Mem.head _)
    have leftFormednessFundamental :
        FundamentalConclusionAtBoundedSucc env bound context typeParam1
          (universeCodeCell level0 flag) :=
      premisesFundamental
        { scope := scope, context := context, subject := typeParam1,
          classifier := universeCodeCell level0 flag }
        (List.Mem.tail _ (List.Mem.head _))
    obtain ⟨secondCandidate, secondTypeReducible, secondMember⟩ :=
      valueFundamental substitution envReducible
    have leftMember :
        IsReducibleMemberAtBounded env bound (universeCodeCell level0 flag)
          (RawTerm.subst substitution typeParam1) :=
      leftFormednessFundamental substitution envReducible
    have belowBound : LevelExpr.denote level0 env < bound := by
      obtain ⟨_, leftUniverseReducible, _⟩ := leftMember
      exact universeCodeReducibleAtBounded_belowBound leftUniverseReducible
    obtain ⟨firstCandidate, firstTypeReducible⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound leftMember belowBound
    refine ⟨reachAwareEitherCandidate firstCandidate secondCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataFlatCarrierAware (combinator := .coproductLike)
        firstTypeReducible secondTypeReducible
    · exact reachAwareEitherCandidate.memberOfReducibleInr
        (ReducibleTypeAtBounded.isReducibilityCandidate secondTypeReducible) secondMember

end FX1Poly.Typed
