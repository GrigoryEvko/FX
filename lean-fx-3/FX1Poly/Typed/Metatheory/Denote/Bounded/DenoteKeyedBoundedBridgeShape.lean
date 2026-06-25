import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedReducibility
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierCombinatorTable
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity

/-! # FX1Poly/Typed/DenoteKeyedBoundedBridgeShape
    — bridge (path-type) type-code inversion for the BOUNDED relation (the pathApp elim-direction port)

The bridge twin of `ReducibleTypeStepBounded.candidateCarrierAwareShape` (in
`DenoteKeyedBoundedCarrierAwareShape`): a `bridgeTypeCell carrier left right`-rooted bound-reducible type came
through the `dataBridgeCarrierAware` arm, so it recovers the carrier candidate as a BOUNDED sub-derivation plus
the `bridgeReducibleCandidate IsStronglyNormalizing`-form `PointwiseIff`.  A DIRECT induction port of the denote
`ReducibleTypeStepDenote.candidateBridgeShape` (the derivation-PRODUCING / forget-bridge dichotomy: this lemma's
output carries a bounded sub-derivation the forget bridge cannot recover, so — like `candidateCarrierAwareShape`
/ `candidatePiShape` — it is ported, not transferred).

The dependent `pathApp` (endpoint-β) elim row on a path scrutinee needs the carrier candidate of the scrutinee's
bridge type to type the endpoint contractum: `pathApp path arg ↝ body[arg]` lands in the carrier candidate, and
the row's `contractumMemberIfReachesPathLam` residue is supplied by `bridgeReducibleCandidate.contractumMemberAt`
— which this inversion extracts from the path's bound-reducible `bridgeTypeCell carrier left right` membership.
The non-dependent (constant) carrier keeps the candidate conversion-invariance-free, so the inversion is total.

## Zero-axiom verification

`candidateBridgeShape` is the same structural induction on `ReducibleTypeStepBounded` as the shipped
`candidateCarrierAwareShape` (verbatim the arm arities; the `dataBridgeCarrierAware` arm binds its carrier
reducible, no induction hypotheses) with the productive role on `dataBridgeCarrierAware`: it EXTRACTS (via
`bridgeTypeCell_inj`), and `piType` / `universeCode` / `dataEmpty` / `dataFlatCarrierAware` / `dataTermIndexed`
close by concrete-root / carrier-combinator clash (`Generator.noConfusion` /
`CarrierCombinator.cell_ne_of_carrierCombinator?_none`), `whnfExpand` by `gen_bridgeCode`-flatness
(`noWeakHeadStep_of_isFlatDataCode rfl`), `neutral` by its `isFlatDataCode = false` gate, and `dataFlat` by its
`isTermIndexedCode = false` gate (`gen_bridgeCode.isTermIndexedCode = true`).  `bridgeTypeInversion` is
`candidateBridgeShape rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Bridge-code shape inversion for the bounded relation (direct induction port).**  A `bridgeTypeCell carrier
left right`-rooted bound-reducible type came through the `dataBridgeCarrierAware` arm; recovers the carrier
candidate as a BOUNDED sub-derivation plus the `bridgeReducibleCandidate IsStronglyNormalizing`-form
`PointwiseIff`.  The bridge twin of `candidateCarrierAwareShape` (productive arm: `dataBridgeCarrierAware`; the
rest close by root mismatch / flatness / term-indexedness). -/
theorem ReducibleTypeStepBounded.candidateBridgeShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ∀ {carrier left right : RawTerm scope},
      typeCode = bridgeTypeCell carrier left right →
      ∃ carrierCandidate : RawTerm scope → Prop,
        ReducibleTypeStepBounded env lowerAt bound carrier carrierCandidate ∧
        PointwiseIff candidate (bridgeReducibleCandidate IsStronglyNormalizing carrierCandidate) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _carrier _left _right hType; subst hType
      exact absurd weakHeadStep0 (noWeakHeadStep_of_isFlatDataCode rfl _)
  | neutral _ _ _ _ notFlat =>
      intro _carrier _left _right hType; subst hType
      exact nomatch notFlat
  | piType _ _ _ _ _ =>
      intro _carrier _left _right hType
      have rootMismatch : Generator.gen_piTyCode = Generator.gen_bridgeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch Generator.noConfusion
  | universeCode _ _ _ =>
      intro _carrier _left _right hType
      have rootMismatch : Generator.gen_universeCode = Generator.gen_bridgeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch Generator.noConfusion
  | dataEmpty =>
      intro _carrier _left _right hType
      have rootMismatch : Generator.gen_emptyCode = Generator.gen_bridgeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch Generator.noConfusion
  | dataFlat _flatPinned _notCarrierAware notTermIndexed =>
      intro _carrier _left _right hType
      rw [hType] at notTermIndexed
      exact nomatch notTermIndexed
  | dataFlatCarrierAware _firstReducible _secondReducible _firstHypothesis _secondHypothesis =>
      intro _carrier _left _right hType
      exact absurd hType (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | dataUnaryCarrierAware _elementReducible =>
      intro _carrier _left _right hType
      exact absurd hType (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | dataTermIndexed =>
      intro _carrier _left _right hType
      have rootMismatch : Generator.gen_idCode = Generator.gen_bridgeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch Generator.noConfusion
  | @dataBridgeCarrierAware carrierArm _leftArm _rightArm carrierCandidateArm carrierReducibleArm
      _carrierHypothesis =>
      intro _carrier _left _right hType
      obtain ⟨carrierEq, _leftEq, _rightEq⟩ := bridgeTypeCell_inj hType
      subst carrierEq
      exact ⟨carrierCandidateArm, carrierReducibleArm, fun _term => Iff.rfl⟩
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _carrier _left _right hType
      obtain ⟨carrierCandidate, carrierReducible, pwi⟩ := innerHypothesis hType
      exact ⟨carrierCandidate, carrierReducible,
        fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- **Bridge-code inversion (existential, bound-indexed).**  A `bridgeTypeCell carrier left right`-rooted
bound-reducible type recovers the carrier candidate (as a bound-reducible sub-derivation) and the
`bridgeReducibleCandidate IsStronglyNormalizing`-form `PointwiseIff`.  The bounded twin of the denote bridge
inversion; `candidateBridgeShape rfl`.  Consumed by the dependent `pathApp` (endpoint-β) elim engine to extract
the scrutinee bridge type's carrier candidate for the endpoint contractum residue. -/
theorem ReducibleTypeAtBounded.bridgeTypeInversion {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {carrier left right : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound (bridgeTypeCell carrier left right) candidate) :
    ∃ carrierCandidate : RawTerm scope → Prop,
      ReducibleTypeAtBounded env bound carrier carrierCandidate ∧
      PointwiseIff candidate (bridgeReducibleCandidate IsStronglyNormalizing carrierCandidate) :=
  reducible.candidateBridgeShape rfl

end FX1Poly.Typed
