import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate

/-! # FX1Poly/Core/CarrierAwareEitherCandidate
    — the carrier-aware coproduct Tait candidate (FTGEN-5.2 substrate, coproduct row)

The flat either code's reducibility candidate shipped in `FlatCodeTaitCandidate` is the CONTENT-FREE
`dataTaitCandidate isEitherValue`: it tracks only "reduces to an `inl`/`inr` value", forgetting whether the
injected PAYLOAD is itself a reducible member of the carrier type (`A` under `inl`, `B` under `inr`).  That
content-freeness is exactly the placeholder the denote-keyed `dataFlat` arm of `ReducibleTypeStepDenote`
inherits at `gen_eitherCode`, and it walls the native fundamental theorem's case-analysis (`eitherMatch`)
eliminator arm: dispatching on `inl a` needs `a ∈ ⟦A⟧` to type the left branch, a fact the weak candidate
does not record.

This file builds the CARRIER-AWARE replacement at the pure candidate level — the coproduct twin of
`carrierAwarePairCandidate`, and the second carrier-aware-candidate row the `CarrierCombinator` table (the
table-driven `dataFlatCarrierAware` arm) will assemble:

  * `eitherValueWithMembers firstCandidate secondCandidate` — the carrier-aware injection predicate: an
    `inl`/`inr` cell whose normal payload satisfies the corresponding carrier candidate.
  * `carrierAwareEitherCandidate firstCandidate secondCandidate` — `dataTaitCandidate` at that predicate, so
    ALL Girard candidate metatheory (CR1/CR2/CR3, head-expansion closure, member multi-step expansion) is
    inherited instantly and uniformly in the carriers.
  * `eitherValueWithMembers_isEitherValue` / `carrierAwareEitherCandidate_toWeakEitherCandidate` — the
    REFINEMENT: every carrier-aware member is a (weak) `dataTaitCandidate isEitherValue` member, so the
    carrier-aware candidate STRENGTHENS the content-free flat-either candidate without dropping any of its
    consumers (it directly supplies the `scrutineeMember` premise the closed-either canonicity extraction
    consumes).
  * `carrierAwareEitherCandidate.memberOfNormalInl` / `.memberOfNormalInr` — the intros: a normal injection
    of a carrier member is a carrier-aware member (the data-intro shapes the `inl`/`inr` constructor FT arms
    produce).
  * `carrierAwareEitherCandidate_congr` — the determinism core: pointwise-equivalent carriers yield
    pointwise-equivalent coproduct candidates (the finisher the table arm's `deterministic` coproduct case
    needs, mirroring `carrierAwarePairCandidate_congr`), without `funext`.

## Zero-axiom verification

Every candidate property is an instance of the shipped generic `dataTaitCandidate` bundle at the carrier-
aware injection predicate; the refinement drops one conjunct of each disjunct; the congruence reuses the
generic `dataTaitCandidate_congr`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware injection predicate.**  A term is a carrier-aware either value when it IS an `inl`
cell whose normal payload lies in `firstCandidate`, OR an `inr` cell whose normal payload lies in
`secondCandidate`.  The strengthening of `isEitherValue` that records payload reducibility — the content the
weak flat-either candidate drops. -/
def eitherValueWithMembers {scope : Nat} (firstCandidate secondCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  (∃ payload : RawTerm scope, term = eitherInlCell payload ∧
      RawTerm.isStepNormalForm payload ∧ firstCandidate payload)
    ∨ (∃ payload : RawTerm scope, term = eitherInrCell payload ∧
      RawTerm.isStepNormalForm payload ∧ secondCandidate payload)

/-- **The carrier-aware coproduct Tait candidate.**  `dataTaitCandidate` at the carrier-aware injection
predicate: "strongly normalizing, and every reachable normal form is a carrier-aware injection or neutral".
Refines the content-free `dataTaitCandidate isEitherValue` (the weak flat-either candidate). -/
def carrierAwareEitherCandidate {scope : Nat} (firstCandidate secondCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate (eitherValueWithMembers firstCandidate secondCandidate)

/-- **The carrier-aware coproduct candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from
the generic `dataTaitCandidate` bundle, uniformly in the carriers. -/
theorem carrierAwareEitherCandidate_isReducibilityCandidate {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (carrierAwareEitherCandidate firstCandidate secondCandidate) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The carrier-aware coproduct candidate is head-expansion-closed** — Π-codomain-ready (the FT's
Π-introduction arm property), instant from the generic theorem. -/
theorem carrierAwareEitherCandidate_headExpansionClosed {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (carrierAwareEitherCandidate firstCandidate secondCandidate) :=
  dataTaitCandidate_headExpansionClosed

/-- **A carrier-aware either value is a (weak) either value** — drop the carrier-membership conjunct from
whichever injection disjunct holds.  The predicate-level half of the refinement. -/
theorem eitherValueWithMembers_isEitherValue {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (carrierAware : eitherValueWithMembers firstCandidate secondCandidate term) :
    isEitherValue term := by
  rcases carrierAware with ⟨payload, termEq, payloadNormal, _payloadMember⟩
    | ⟨payload, termEq, payloadNormal, _payloadMember⟩
  · exact Or.inl ⟨payload, termEq, payloadNormal⟩
  · exact Or.inr ⟨payload, termEq, payloadNormal⟩

/-- **★ Refinement: every carrier-aware either member is a (weak) `dataTaitCandidate isEitherValue` member.**
Carries each reachable normal form's carrier-aware-injection-or-neutral disjunct down to injection-or-neutral
via `eitherValueWithMembers_isEitherValue`, so the carrier-aware candidate STRENGTHENS the content-free
flat-either candidate — and directly supplies the `scrutineeMember` premise the closed-either canonicity
extraction consumes. -/
theorem carrierAwareEitherCandidate_toWeakEitherCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : carrierAwareEitherCandidate firstCandidate secondCandidate term) :
    dataTaitCandidate isEitherValue term := by
  refine ⟨member.1, ?_⟩
  intro normalForm reachesNF nfIsNormal
  rcases member.2 normalForm reachesNF nfIsNormal with isCarrierEither | isNeutral
  · exact Or.inl (eitherValueWithMembers_isEitherValue isCarrierEither)
  · exact Or.inr isNeutral

/-- **A normal `inl` of a carrier member is a carrier-aware member.**  An injection value `eitherInlCell
payload` with normal payload in the first carrier is a carrier-aware coproduct member (a structural normal
form, strongly normalizing, reducing only to itself — a carrier-aware injection).  The data-intro shape the
`inl` constructor FT arm produces. -/
theorem carrierAwareEitherCandidate.memberOfNormalInl {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {payload : RawTerm scope}
    (cellIsNormal : RawTerm.isStepNormalForm (eitherInlCell payload))
    (payloadNormal : RawTerm.isStepNormalForm payload) (payloadMember : firstCandidate payload) :
    carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInlCell payload) :=
  dataTaitCandidate.memberOfValue cellIsNormal
    (Or.inl ⟨payload, rfl, payloadNormal, payloadMember⟩)

/-- **A normal `inr` of a carrier member is a carrier-aware member.**  The right-injection twin of
`memberOfNormalInl` — the data-intro shape the `inr` constructor FT arm produces. -/
theorem carrierAwareEitherCandidate.memberOfNormalInr {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {payload : RawTerm scope}
    (cellIsNormal : RawTerm.isStepNormalForm (eitherInrCell payload))
    (payloadNormal : RawTerm.isStepNormalForm payload) (payloadMember : secondCandidate payload) :
    carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInrCell payload) :=
  dataTaitCandidate.memberOfValue cellIsNormal
    (Or.inr ⟨payload, rfl, payloadNormal, payloadMember⟩)

/-- **The carrier-aware injection predicate is congruent in its carriers.**  Pointwise-equivalent carrier
candidates yield pointwise-equivalent carrier-aware injection predicates — the payload-membership conjunct of
each disjunct swaps under the respective carrier iff, the injection-shape and payload-normality conjuncts are
untouched. -/
theorem eitherValueWithMembers_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (eitherValueWithMembers firstCandidate1 secondCandidate1)
      (eitherValueWithMembers firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro (⟨payload, termEq, payloadNormal, payloadMember⟩ | ⟨payload, termEq, payloadNormal, payloadMember⟩)
    · exact Or.inl ⟨payload, termEq, payloadNormal, (firstIff payload).mp payloadMember⟩
    · exact Or.inr ⟨payload, termEq, payloadNormal, (secondIff payload).mp payloadMember⟩
  · rintro (⟨payload, termEq, payloadNormal, payloadMember⟩ | ⟨payload, termEq, payloadNormal, payloadMember⟩)
    · exact Or.inl ⟨payload, termEq, payloadNormal, (firstIff payload).mpr payloadMember⟩
    · exact Or.inr ⟨payload, termEq, payloadNormal, (secondIff payload).mpr payloadMember⟩

/-- **★ The carrier-aware coproduct candidate is congruent in its carriers (the determinism core).**  When the
carrier candidates are pointwise-equivalent, the carrier-aware coproduct candidates are pointwise-equivalent —
the coproduct twin of `carrierAwarePairCandidate_congr` and exactly the finishing lemma the table-driven
`dataFlatCarrierAware` arm's `deterministic` coproduct case will need: a coproduct-shape inversion recovers
both derivations' carrier candidates, the carrier induction hypotheses align them pointwise, and this lemma
transports that alignment onto the denoted coproduct candidate — without `funext`. -/
theorem carrierAwareEitherCandidate_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (carrierAwareEitherCandidate firstCandidate1 secondCandidate1)
      (carrierAwareEitherCandidate firstCandidate2 secondCandidate2) :=
  dataTaitCandidate_congr (eitherValueWithMembers_congr firstIff secondIff)

end FX1Poly.Core
