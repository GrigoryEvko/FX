import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedReducibility
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierCombinatorTable
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierModelAssembler
import FX1Poly.Core.Metatheory.Reducibility.Candidates.UnaryCarrierCombinatorTable

/-! # FX1Poly/Typed/DenoteKeyedBoundedCarrierAwareShape
    — carrier-aware (data combinator) type-code inversion for the BOUNDED relation (the elim-direction port)

The carrier-aware twin of `ReducibleTypeStepBounded.candidatePiShape` (in `DenoteKeyedBoundedPiElimArm`): a
`combinator.cell`-rooted bound-reducible type — `product(A,B)` / `either(A,B)` / `equiv(A,B)`, the three
`CarrierCombinator` heads — came through the `dataFlatCarrierAware` arm, so it recovers the TWO component
candidates as BOUNDED sub-derivations plus the application-form `PointwiseIff` against
`combinator.assemble`.  A DIRECT induction port of the denote `candidateCarrierAwareShape` (the
derivation-PRODUCING / forget-bridge dichotomy: this lemma's output carries bounded sub-derivations the forget
bridge cannot recover, so — like `candidatePiShape` — it is ported, not transferred).

The dependent data eliminators on a parameterized scrutinee type (`eitherMatch` on `either(A,B)`, `fst`/`snd`
on `product(A,B)`) need the component candidate of the scrutinee's type to type the branch application: the
branch is a Π over the component type `A`, and applying it to the injected payload needs the payload's
membership in `A`'s candidate — which this inversion extracts from the scrutinee's bound-reducible
`either(A,B)` / `product(A,B)` membership.  Generic over the combinator, so all three carrier formers (and the
eventual unary option/list once the arm goes arity-generic) reuse it.

## Zero-axiom verification

`candidateCarrierAwareShape` is an 8-arm structural induction on `ReducibleTypeStepBounded` — verbatim the arm
arities of the shipped `candidatePiShape` (the `dataFlatCarrierAware` arm binds exactly its two component
reducibles, no induction hypotheses, the bounded eliminator's shape) with the productive/absurd roles swapped:
the `dataFlatCarrierAware` arm EXTRACTS (via `CarrierCombinator.cell_inj`), and `piType` / `universeCode` /
`dataEmpty` / `dataFlat` / `neutral` / `whnfExpand` close by root mismatch (`cell_ne_of_carrierCombinator?_none`
/ `cell_carrierCombinator?_ne_none` / `cell_isFlatDataCode` / `cell_noWeakHeadStep`).  `carrierAwareTypeInversion`
is `candidateCarrierAwareShape rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Carrier-aware-code shape inversion for the bounded relation (direct induction port).**  A
`combinator.cell`-rooted bound-reducible type came through the `dataFlatCarrierAware` arm; recovers the
first/second component candidates as BOUNDED sub-derivations plus the `assemble`-form `PointwiseIff`.  Eight-arm
induction on `ReducibleTypeStepBounded`, the carrier-aware twin of `candidatePiShape` (productive arm:
`dataFlatCarrierAware`; the rest close by root mismatch). -/
theorem ReducibleTypeStepBounded.candidateCarrierAwareShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ∀ {combinator : CarrierCombinator} {firstCode secondCode : RawTerm scope},
      typeCode = combinator.cell firstCode secondCode →
      ∃ (firstCandidate secondCandidate : RawTerm scope → Prop),
        ReducibleTypeStepBounded env lowerAt bound firstCode firstCandidate ∧
        ReducibleTypeStepBounded env lowerAt bound secondCode secondCandidate ∧
        PointwiseIff candidate (combinator.assembleModel firstCandidate secondCandidate) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _combinator _firstCode _secondCode hType; subst hType
      exact absurd weakHeadStep0 (CarrierCombinator.cell_noWeakHeadStep _ _ _ _)
  | neutral _ _ _ _ notFlat =>
      intro _combinator _firstCode _secondCode hType; subst hType
      exact absurd ((CarrierCombinator.cell_isFlatDataCode _ _ _).symm.trans notFlat) (by decide)
  | piType _ _ _ _ _ =>
      intro _combinator _firstCode _secondCode hType
      exact absurd hType.symm (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | universeCode _ _ _ =>
      intro _combinator _firstCode _secondCode hType
      exact absurd hType.symm (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | dataEmpty =>
      intro _combinator _firstCode _secondCode hType
      exact absurd hType.symm (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | dataFlat _flatPinned notCarrierAware =>
      intro _combinator _firstCode _secondCode hType
      rw [hType] at notCarrierAware
      exact absurd notCarrierAware (CarrierCombinator.cell_carrierCombinator?_ne_none _ _ _)
  | dataFlatCarrierAware firstReducible secondReducible =>
      intro _combinator _firstCode _secondCode hType
      obtain ⟨combinatorEq, firstEq, secondEq⟩ := CarrierCombinator.cell_inj hType
      subst combinatorEq; subst firstEq; subst secondEq
      exact ⟨_, _, firstReducible, secondReducible, fun _term => Iff.rfl⟩
  | dataUnaryCarrierAware _elementReducible =>
      intro _combinator _firstCode _secondCode hType
      have clash := congrArg Generator.carrierCombinator? (congrArg RawTerm.rootGenerator hType)
      rw [UnaryCarrierCombinator.cell_carrierCombinator?_eq_none] at clash
      exact absurd clash.symm (CarrierCombinator.cell_carrierCombinator?_ne_none _ _ _)
  | dataTermIndexed =>
      intro _combinator _firstCode _secondCode hType
      exact absurd hType.symm (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | dataBridgeCarrierAware _carrierReducible =>
      intro _combinator _firstCode _secondCode hType
      exact absurd hType.symm (CarrierCombinator.cell_ne_of_carrierCombinator?_none _ _ _ rfl)
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _combinator _firstCode _secondCode hType
      obtain ⟨firstCandidate, secondCandidate, firstReducible, secondReducible, pwi⟩ :=
        innerHypothesis hType
      exact ⟨firstCandidate, secondCandidate, firstReducible, secondReducible,
        fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- **Carrier-aware code inversion (existential, bound-indexed).**  A `combinator.cell`-rooted bound-reducible
type recovers the first/second component candidates (as bound-reducible sub-derivations) and the `assemble`-form
`PointwiseIff`.  The bounded twin of the denote carrier-aware inversion; `candidateCarrierAwareShape rfl`.
Consumed by the dependent data-eliminator bridges (`eitherMatch` / `fst` / `snd`) to extract the scrutinee
type's component candidate for the branch application. -/
theorem ReducibleTypeAtBounded.carrierAwareTypeInversion {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {combinator : CarrierCombinator} {firstCode secondCode : RawTerm scope}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound (combinator.cell firstCode secondCode) candidate) :
    ∃ (firstCandidate secondCandidate : RawTerm scope → Prop),
      ReducibleTypeAtBounded env bound firstCode firstCandidate ∧
      ReducibleTypeAtBounded env bound secondCode secondCandidate ∧
      PointwiseIff candidate (combinator.assembleModel firstCandidate secondCandidate) :=
  reducible.candidateCarrierAwareShape rfl

/-- **Unary carrier-aware-code shape inversion for the bounded relation (direct induction port).**  A
`combinator.cell`-rooted bound-reducible type — the option (and, after swap 4, list) head — came through the
`dataUnaryCarrierAware` arm; recovers the SINGLE element candidate as a BOUNDED sub-derivation plus the
`assembleModel`-form `PointwiseIff`.  The arity-1 twin of `candidateCarrierAwareShape`: the productive arm is
`dataUnaryCarrierAware`, and the rest close by root mismatch (`dataFlat` by its `notUnaryCarrierAware` gate,
`dataFlatCarrierAware` by the cross-table `carrierCombinator? = none` clash, the others by the unary cell's
`unaryCarrierCombinator? = some _` round-trip). -/
theorem ReducibleTypeStepBounded.candidateUnaryCarrierAwareShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ∀ {combinator : UnaryCarrierCombinator} {elementCode : RawTerm scope},
      typeCode = combinator.cell elementCode →
      ∃ (elementCandidate : RawTerm scope → Prop),
        ReducibleTypeStepBounded env lowerAt bound elementCode elementCandidate ∧
        PointwiseIff candidate (combinator.assembleModel elementCandidate) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _combinator _elementCode hType; subst hType
      exact absurd weakHeadStep0 (UnaryCarrierCombinator.cell_noWeakHeadStep _ _ _)
  | neutral _ _ _ _ notFlat =>
      intro _combinator _elementCode hType; subst hType
      exact absurd ((UnaryCarrierCombinator.cell_isFlatDataCode _ _).symm.trans notFlat) (by decide)
  | piType _ _ _ _ _ =>
      intro _combinator _elementCode hType
      exact absurd hType.symm (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | universeCode _ _ _ =>
      intro _combinator _elementCode hType
      exact absurd hType.symm (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | dataEmpty =>
      intro _combinator _elementCode hType
      exact absurd hType.symm (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | dataFlat _flatPinned _notCarrierAware _notTermIndexed notUnaryCarrierAware =>
      intro _combinator _elementCode hType
      rw [hType] at notUnaryCarrierAware
      exact absurd notUnaryCarrierAware (UnaryCarrierCombinator.cell_unaryCarrierCombinator?_ne_none _ _)
  | dataFlatCarrierAware firstReducible secondReducible =>
      intro _combinator _elementCode hType
      have clash := congrArg Generator.carrierCombinator? (congrArg RawTerm.rootGenerator hType)
      rw [UnaryCarrierCombinator.cell_carrierCombinator?_eq_none] at clash
      exact absurd clash (CarrierCombinator.cell_carrierCombinator?_ne_none _ _ _)
  | dataUnaryCarrierAware elementReducible =>
      intro _combinator _elementCode hType
      obtain ⟨combinatorEq, elementEq⟩ := UnaryCarrierCombinator.cell_inj hType
      subst combinatorEq; subst elementEq
      exact ⟨_, elementReducible, fun _term => Iff.rfl⟩
  | dataTermIndexed =>
      intro _combinator _elementCode hType
      exact absurd hType.symm (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | dataBridgeCarrierAware _carrierReducible =>
      intro _combinator _elementCode hType
      exact absurd hType.symm (UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none _ _ rfl)
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _combinator _elementCode hType
      obtain ⟨elementCandidate, elementReducible, pwi⟩ := innerHypothesis hType
      exact ⟨elementCandidate, elementReducible, fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- **Unary carrier-aware code inversion (existential, bound-indexed).**  A `combinator.cell`-rooted
bound-reducible type recovers the element candidate (as a bound-reducible sub-derivation) and the
`assembleModel`-form `PointwiseIff`.  The arity-1 twin of `carrierAwareTypeInversion`;
`candidateUnaryCarrierAwareShape rfl`.  Consumed by the dependent `optionMatch` scrutinee bridge to recover the
reach-aware option candidate from the scrutinee's bound-reducible `option(A)` membership. -/
theorem ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {combinator : UnaryCarrierCombinator} {elementCode : RawTerm scope}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound (combinator.cell elementCode) candidate) :
    ∃ (elementCandidate : RawTerm scope → Prop),
      ReducibleTypeAtBounded env bound elementCode elementCandidate ∧
      PointwiseIff candidate (combinator.assembleModel elementCandidate) :=
  reducible.candidateUnaryCarrierAwareShape rfl

end FX1Poly.Typed
