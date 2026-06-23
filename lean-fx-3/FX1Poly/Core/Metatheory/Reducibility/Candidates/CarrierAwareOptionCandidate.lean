import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Canonicity.OptionCanonicalFormsCandidate

/-! # FX1Poly/Core/CarrierAwareOptionCandidate
    — the carrier-aware option Tait candidate (DEP-OPTION-MODEL substrate, the UNARY carrier-aware row)

The flat option code's content-free candidate (`CanonicalFormsPredicate isOptionValue`,
`OptionCanonicalFormsCandidate`) tracks only "reduces to `none`/`some`", forgetting whether the injected
PAYLOAD under `some` is itself a reducible member of the carrier type `A`.  That content-freeness walls the
native fundamental theorem's `optionMatch` eliminator arm: dispatching on `some payload` needs
`payload ∈ ⟦A⟧` to type the some-branch, a fact the weak candidate does not record — exactly the gap the
carrier-aware coproduct candidate (`CarrierAwareEitherCandidate`) fills for `eitherMatch`.

This file builds the UNARY carrier-aware option candidate — the option twin of `carrierAwareEitherCandidate`,
specialized to ONE carrier (option(A) has a single type parameter, unlike the binary product/either/equiv).
It is a `dataTaitCandidate` (NOT the `CanonicalFormsPredicate`-based `optionCanonicalFormsCandidate`) so it
slots into the SAME carrier-aware-candidate metatheory the binary table dispatches to, and so the future
arity-generic carrier-aware reducibility arm assembles it uniformly with the binary formers:

  * `optionValueWithMember carrierCandidate` — the carrier-aware option predicate: `none`, or a `some` cell
    whose normal payload satisfies the carrier candidate.
  * `carrierAwareOptionCandidate carrierCandidate` — `dataTaitCandidate` at that predicate, so ALL Girard
    candidate metatheory (CR1/CR2/CR3, head-expansion closure, member multi-step expansion) is inherited
    instantly and uniformly in the carrier.
  * `optionValueWithMember_isOptionValue` / `carrierAwareOptionCandidate_toWeakOptionCandidate` — the
    REFINEMENT: every carrier-aware member is a (weak) `dataTaitCandidate isOptionValue` member, so the
    carrier-aware candidate STRENGTHENS the content-free flat-option candidate without dropping any of its
    consumers (it directly supplies the `scrutineeMember` premise the closed-option canonicity extraction
    consumes).
  * `carrierAwareOptionCandidate.memberOfNormalNone` / `.memberOfNormalSome` — the intros: `none`, and a
    normal `some` of a carrier member, are carrier-aware members (the data-intro shapes the `none`/`some`
    constructor FT arms produce).
  * `carrierAwareOptionCandidate_congr` — the determinism core: a pointwise-equivalent carrier yields a
    pointwise-equivalent option candidate (the finisher the future arity-generic arm's `deterministic`
    option case needs, mirroring `carrierAwareEitherCandidate_congr`), without `funext`.

## Zero-axiom verification

Every candidate property is an instance of the shipped generic `dataTaitCandidate` bundle at the carrier-
aware option predicate; the refinement drops the carrier conjunct of the `some` disjunct; the congruence
reuses the generic `dataTaitCandidate_congr`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware option predicate.**  A term is a carrier-aware option value when it IS the `none`
cell, OR a `some` cell whose normal payload lies in `carrierCandidate`.  The strengthening of `isOptionValue`
that records payload reducibility — the content the weak flat-option candidate drops. -/
def optionValueWithMember {scope : Nat} (carrierCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  term = optionNoneCell
    ∨ (∃ payload : RawTerm scope, term = optionSomeCell payload ∧
        RawTerm.isStepNormalForm payload ∧ carrierCandidate payload)

/-- **The carrier-aware option Tait candidate.**  `dataTaitCandidate` at the carrier-aware option predicate:
"strongly normalizing, and every reachable normal form is a carrier-aware option value or neutral".  Refines
the content-free option candidate. -/
def carrierAwareOptionCandidate {scope : Nat} (carrierCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate (optionValueWithMember carrierCandidate)

/-- **The carrier-aware option candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from
the generic `dataTaitCandidate` bundle, uniformly in the carrier. -/
theorem carrierAwareOptionCandidate_isReducibilityCandidate {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (carrierAwareOptionCandidate carrierCandidate) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The carrier-aware option candidate is head-expansion-closed** — Π-codomain-ready (the FT's
Π-introduction arm property), instant from the generic theorem. -/
theorem carrierAwareOptionCandidate_headExpansionClosed {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (carrierAwareOptionCandidate carrierCandidate) :=
  dataTaitCandidate_headExpansionClosed

/-- **A carrier-aware option value is a (weak) option value** — drop the carrier-membership conjunct from the
`some` disjunct.  The predicate-level half of the refinement. -/
theorem optionValueWithMember_isOptionValue {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (carrierAware : optionValueWithMember carrierCandidate term) :
    isOptionValue term := by
  rcases carrierAware with termIsNone | ⟨payload, termEq, payloadNormal, _payloadMember⟩
  · exact Or.inl termIsNone
  · exact Or.inr ⟨payload, termEq, payloadNormal⟩

/-- **★ Refinement: every carrier-aware option member is a (weak) `dataTaitCandidate isOptionValue` member.**
Carries each reachable normal form's carrier-aware-option-or-neutral disjunct down to option-or-neutral via
`optionValueWithMember_isOptionValue`, so the carrier-aware candidate STRENGTHENS the content-free flat-option
candidate — and directly supplies the `scrutineeMember` premise the closed-option canonicity extraction
consumes. -/
theorem carrierAwareOptionCandidate_toWeakOptionCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : carrierAwareOptionCandidate carrierCandidate term) :
    dataTaitCandidate isOptionValue term := by
  refine ⟨member.1, ?_⟩
  intro normalForm reachesNF nfIsNormal
  rcases member.2 normalForm reachesNF nfIsNormal with isCarrierOption | isNeutral
  · exact Or.inl (optionValueWithMember_isOptionValue isCarrierOption)
  · exact Or.inr isNeutral

/-- **The `none` cell is a carrier-aware option member.**  A structural normal form reducing only to itself —
a carrier-aware option value.  The data-intro shape the `none` constructor FT arm produces. -/
theorem carrierAwareOptionCandidate.memberOfNormalNone {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (cellIsNormal : RawTerm.isStepNormalForm (optionNoneCell (scope := scope))) :
    carrierAwareOptionCandidate carrierCandidate optionNoneCell :=
  dataTaitCandidate.memberOfValue cellIsNormal (Or.inl rfl)

/-- **A normal `some` of a carrier member is a carrier-aware option member.**  An injection value
`optionSomeCell payload` with normal payload in the carrier is a carrier-aware option member — the data-intro
shape the `some` constructor FT arm produces. -/
theorem carrierAwareOptionCandidate.memberOfNormalSome {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {payload : RawTerm scope}
    (cellIsNormal : RawTerm.isStepNormalForm (optionSomeCell payload))
    (payloadNormal : RawTerm.isStepNormalForm payload) (payloadMember : carrierCandidate payload) :
    carrierAwareOptionCandidate carrierCandidate (optionSomeCell payload) :=
  dataTaitCandidate.memberOfValue cellIsNormal
    (Or.inr ⟨payload, rfl, payloadNormal, payloadMember⟩)

/-- **The carrier-aware option predicate is congruent in its carrier.**  A pointwise-equivalent carrier
candidate yields a pointwise-equivalent carrier-aware option predicate — the payload-membership conjunct of
the `some` disjunct swaps under the carrier iff, the `none` shape and the injection-shape/payload-normality
conjuncts are untouched. -/
theorem optionValueWithMember_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (optionValueWithMember carrierCandidate1) (optionValueWithMember carrierCandidate2) := by
  intro term
  constructor
  · rintro (termIsNone | ⟨payload, termEq, payloadNormal, payloadMember⟩)
    · exact Or.inl termIsNone
    · exact Or.inr ⟨payload, termEq, payloadNormal, (carrierIff payload).mp payloadMember⟩
  · rintro (termIsNone | ⟨payload, termEq, payloadNormal, payloadMember⟩)
    · exact Or.inl termIsNone
    · exact Or.inr ⟨payload, termEq, payloadNormal, (carrierIff payload).mpr payloadMember⟩

/-- **★ The carrier-aware option candidate is congruent in its carrier (the determinism core).**  When the
carrier candidate is pointwise-equivalent, the carrier-aware option candidates are pointwise-equivalent — the
option twin of `carrierAwareEitherCandidate_congr` and exactly the finishing lemma the future arity-generic
carrier-aware arm's `deterministic` option case will need: an option-shape inversion recovers both
derivations' carrier candidate, the carrier induction hypothesis aligns them pointwise, and this lemma
transports that alignment onto the denoted option candidate — without `funext`. -/
theorem carrierAwareOptionCandidate_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (carrierAwareOptionCandidate carrierCandidate1)
      (carrierAwareOptionCandidate carrierCandidate2) :=
  dataTaitCandidate_congr (optionValueWithMember_congr carrierIff)

end FX1Poly.Core
