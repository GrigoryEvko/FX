import FX1Poly.Typed.Metatheory.Denote.Core.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedLowerAtCongruence
    — the denote reducibility relation transports across pointwise-equal below-family parameters
      (the relation-generic transport substrate under universe cumulativity; toward #753/SN-D5e)

`ReducibleTypeAtDenote env level` is `ReducibleTypeStepDenote env (denoteBelowFamily env level)` — the step
functor over a BELOW-FAMILY parameter `lowerAt`.  Whether a type's reducibility-as-a-type transports from one
ambient level to another is therefore exactly whether the two ambient levels' below-families agree on the
indices the derivation reaches.  This file isolates that as a single relation-generic congruence:
`ReducibleTypeStepDenote.lowerAtCongr` transports a whole derivation across ANY two `lowerAt` parameters that
are pointwise-equal as relations.

## Why this is the cumulativity substrate (and where the obstruction lives)

Every arm of `ReducibleTypeStepDenote` is `lowerAt`-congruent: the `neutral` / `dataEmpty` / `dataFlat` arms
never mention `lowerAt`; `whnfExpand` / `piType` / `dataFlatCarrierAware` / `ofPointwiseIff` recurse on their
sub-derivations; and the `universeCode` arm reaches `lowerAt` only at the single fixed index
`LevelExpr.denote levelExpr env`, so two pointwise-equal parameters give pointwise-equal universe candidates
(swapped back through the relation's own `ofPointwiseIff`).  So the transport is UNCONDITIONAL in the parameter
agreement — no induction-recursion, no fuel.

This pins the cumulativity obstruction (`DenoteKeyedCumulativityObstruction`) exactly.  Lifting reducibility
from ambient `lower` to ambient `higher` is transport from `denoteBelowFamily env lower` to
`denoteBelowFamily env higher`, and those two below-families AGREE on every index strictly below `lower`
(`denoteBelowFamily_eq_reducible` rewrites both to the same relation there) but DISAGREE at a gap index in
`[lower, higher)` (the lower family is empty there, the higher is not).  So cumulativity holds whenever the
derivation's universe codes are all below the lower ambient level (the bounded regime — the positive complement
`DenoteKeyedUniverseBoundedCumulativity`), and the gap regime is precisely where the parameter agreement —
hence this congruence's hypothesis — fails.  This is the model-internal transport lemma the #753 bound-carrying
universe arm consumes: its admitted universes are bound-below-ambient by construction, so its parameters always
agree and `lowerAtCongr` carries every member across with no per-shape re-derivation.

## Zero-axiom verification

One `induction reducible with` over the eight arms (the same shape as `deterministic` / `forwardStepStar`),
each arm re-applying its constructor on the inductive hypotheses; the `universeCode` arm swaps the
parameter-indexed candidate via `ofPointwiseIff` and an anonymous-constructor `Iff` over the pointwise
parameter agreement (`dsimp only [universeDenotePredicate]`, no `simp`/`funext`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The denote reducibility step functor transports across pointwise-equal below-family parameters.**
If `lowerAt1` and `lowerAt2` agree as relations at every index, a `ReducibleTypeStepDenote env lowerAt1`
derivation re-derives over `lowerAt2` at the SAME type code and candidate.  The relation-generic transport
substrate under universe cumulativity: the hypothesis `lowerAgree` holds exactly when the two ambient levels'
below-families agree (the bounded regime) and fails exactly at a gap index (the cumulativity obstruction). -/
theorem ReducibleTypeStepDenote.lowerAtCongr {scope : Nat} {env : Nat → Nat}
    {lowerAt1 lowerAt2 : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerAgree : ∀ (lvl : Nat) (typeCode : RawTerm scope) (candidate : RawTerm scope → Prop),
      lowerAt1 lvl typeCode candidate ↔ lowerAt2 lvl typeCode candidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt1 typeCode candidate) :
    ReducibleTypeStepDenote env lowerAt2 typeCode candidate := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact ReducibleTypeStepDenote.whnfExpand weakHeadStep reductInductiveHypothesis
  | neutral noWeakHeadStep notPiType notUniverse notEmpty notFlat =>
      exact ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty notFlat
  | piType codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact ReducibleTypeStepDenote.piType codomainCandidate domainInductiveHypothesis
        codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      refine ReducibleTypeStepDenote.ofPointwiseIff
        (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun universeMember => ?_)
      dsimp only [universeDenotePredicate]
      exact ⟨fun ⟨stronglyNormalizing, candidateWitness, member⟩ =>
          ⟨stronglyNormalizing, candidateWitness,
            (lowerAgree _ universeMember candidateWitness).mpr member⟩,
        fun ⟨stronglyNormalizing, candidateWitness, member⟩ =>
          ⟨stronglyNormalizing, candidateWitness,
            (lowerAgree _ universeMember candidateWitness).mp member⟩⟩
  | dataEmpty =>
      exact ReducibleTypeStepDenote.dataEmpty
  | dataFlat flatPinned notCarrierAware notTermIndexed =>
      exact ReducibleTypeStepDenote.dataFlat flatPinned notCarrierAware notTermIndexed
  | dataFlatCarrierAware _firstReducible _secondReducible
      firstInductiveHypothesis secondInductiveHypothesis =>
      exact ReducibleTypeStepDenote.dataFlatCarrierAware firstInductiveHypothesis
        secondInductiveHypothesis
  | dataTermIndexed =>
      exact ReducibleTypeStepDenote.dataTermIndexed
  | dataBridgeCarrierAware _carrierReducible carrierInductiveHypothesis =>
      exact ReducibleTypeStepDenote.dataBridgeCarrierAware carrierInductiveHypothesis
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact ReducibleTypeStepDenote.ofPointwiseIff innerInductiveHypothesis pointwiseIff

end FX1Poly.Typed
