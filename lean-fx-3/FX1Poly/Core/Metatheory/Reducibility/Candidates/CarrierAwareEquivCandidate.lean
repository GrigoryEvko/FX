import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication

/-! # FX1Poly/Core/CarrierAwareEquivCandidate
    — the carrier-aware equivalence Tait candidate (FTGEN-5.4 substrate, equivalence row)

The flat equiv code's reducibility candidate shipped in `FlatCodeTaitCandidate` is the CONTENT-FREE
`dataTaitCandidate isEquivIntroValue`: it tracks only "reduces to an `equivIntro(forward, backward)` value",
forgetting whether the two injected COMPONENTS are themselves reducible FUNCTIONS between the carrier types
(`forward : A → B`, `backward : B → A`).  That content-freeness is exactly the placeholder the denote-keyed
`dataFlat` arm of `ReducibleTypeStepDenote` inherits at `gen_equivCode`, and it walls the native fundamental
theorem's equivalence-elimination arm (`equivApp`): applying `equivIntro(forward, backward)` to an `a ∈ ⟦A⟧`
needs `forward a ∈ ⟦B⟧`, a fact the weak candidate does not record.

This file builds the CARRIER-AWARE replacement at the pure candidate level — the equivalence cousin of
`carrierAwarePairCandidate` / `carrierAwareEitherCandidate`, and the third carrier-aware-candidate row the
`CarrierCombinator` table (the table-driven `dataFlatCarrierAware` arm, FTGEN-5.5) will assemble.  Unlike the
pair (whose components ARE carrier members) and the coproduct (whose payload IS a carrier member), the equiv
components are FUNCTIONS between the carriers, so the carrier-aware predicate records the ARROW-candidate
membership `fun f => ∀ a, P a → Q (f a)` of each — the `(f, isEquiv f)`-unfold of an equivalence respecting
the carriers (fx_design §3.7 equivalence-as-Σ, realized at the reducibility-candidate level):

  * `equivValueWithMembers domainCandidate codomainCandidate` — the carrier-aware equivalence predicate: an
    `equivIntro(forward, backward)` cell whose normal forward maps the domain candidate into the codomain
    candidate (under application) and whose normal backward maps the codomain candidate into the domain
    candidate.  The `(f, isEquiv f)` Σ-unfold, both components respecting the carriers from FTGEN-5.1.
  * `carrierAwareEquivCandidate domainCandidate codomainCandidate` — `dataTaitCandidate` at that predicate, so
    ALL Girard candidate metatheory (CR1/CR2/CR3, head-expansion closure, member multi-step expansion) is
    inherited instantly and uniformly in the carriers.
  * `equivValueWithMembers_isEquivIntroValue` / `carrierAwareEquivCandidate_toWeakEquivCandidate` — the
    REFINEMENT: every carrier-aware member is a (weak) `dataTaitCandidate isEquivIntroValue` member, so the
    carrier-aware candidate STRENGTHENS the content-free flat-equiv candidate without dropping any consumer.
  * `carrierAwareEquivCandidate.memberOfNormalEquivIntro` — the intro: a normal `equivIntro` of two
    carrier-respecting functions is a carrier-aware member (the equiv-intro shape the `equivIntro` FT arm
    produces).
  * `carrierAwareEquivCandidate.closedReducesToEquivIntro` — the canonical-form theorem at the candidate
    level: a closed carrier-aware member reduces to an `equivIntro` value (the equiv twin of the closed
    coproduct canonicity, the model leg the FTGEN-5.5 type dispatch consumes).
  * `carrierAwareEquivCandidate_congr` — the determinism core: pointwise-equivalent carriers yield
    pointwise-equivalent equivalence candidates (the finisher the table arm's `deterministic` equivalence case
    needs, cousin of `carrierAwarePairCandidate_congr`), without `funext`.  The function-respect conjuncts
    transport along the carrier iffs in BOTH directions (the carrier sits negatively in each function's
    domain hypothesis and positively in its codomain conclusion — both legs of the bidirectional iff are used).

## Zero-axiom verification

Every candidate property is an instance of the shipped generic `dataTaitCandidate` bundle at the carrier-
aware equivalence predicate; the refinement drops the function-respect conjuncts; the congruence transports
each arrow-candidate `∀`-conjunct along the carrier iffs.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware equivalence predicate.**  A term is a carrier-aware equivalence value when it IS an
`equivIntro(forwardFn, backwardFn)` cell whose normal `forwardFn` maps every `domainCandidate` member to a
`codomainCandidate` member (under application), and whose normal `backwardFn` maps every `codomainCandidate`
member to a `domainCandidate` member.  The strengthening of `isEquivIntroValue` that records the components'
reducibility-as-functions — the `(f, isEquiv f)` Σ-unfold of an equivalence respecting the carriers (the
content the weak flat-equiv candidate drops). -/
def equivValueWithMembers {scope : Nat} (domainCandidate codomainCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  ∃ forwardFn backwardFn : RawTerm scope, term = equivIntroValueCell forwardFn backwardFn ∧
    RawTerm.isStepNormalForm forwardFn ∧ RawTerm.isStepNormalForm backwardFn ∧
    (∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate (applicationCell forwardFn argument)) ∧
    (∀ argument : RawTerm scope, codomainCandidate argument →
        domainCandidate (applicationCell backwardFn argument))

/-- **The carrier-aware equivalence Tait candidate.**  `dataTaitCandidate` at the carrier-aware equivalence
predicate: "strongly normalizing, and every reachable normal form is a carrier-aware `equivIntro` or neutral".
Refines the content-free `dataTaitCandidate isEquivIntroValue` (the weak flat-equiv candidate). -/
def carrierAwareEquivCandidate {scope : Nat} (domainCandidate codomainCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate (equivValueWithMembers domainCandidate codomainCandidate)

/-- **The carrier-aware equivalence candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from
the generic `dataTaitCandidate` bundle, uniformly in the carriers. -/
theorem carrierAwareEquivCandidate_isReducibilityCandidate {scope : Nat}
    (domainCandidate codomainCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (carrierAwareEquivCandidate domainCandidate codomainCandidate) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The carrier-aware equivalence candidate is head-expansion-closed** — Π-codomain-ready (the FT's
Π-introduction arm property), instant from the generic theorem. -/
theorem carrierAwareEquivCandidate_headExpansionClosed {scope : Nat}
    (domainCandidate codomainCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (carrierAwareEquivCandidate domainCandidate codomainCandidate) :=
  dataTaitCandidate_headExpansionClosed

/-- **A carrier-aware equivalence value is a (weak) equiv-intro value** — drop the two function-respect
conjuncts.  The predicate-level half of the refinement. -/
theorem equivValueWithMembers_isEquivIntroValue {scope : Nat}
    {domainCandidate codomainCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (carrierAware : equivValueWithMembers domainCandidate codomainCandidate term) :
    isEquivIntroValue term := by
  obtain ⟨forwardFn, backwardFn, termEq, _forwardNormal, _backwardNormal, _forwardResp, _backwardResp⟩ :=
    carrierAware
  exact ⟨forwardFn, backwardFn, termEq⟩

/-- **★ Refinement: every carrier-aware equiv member is a (weak) `dataTaitCandidate isEquivIntroValue`
member.**  Carries each reachable normal form's carrier-aware-`equivIntro`-or-neutral disjunct down to
`equivIntro`-or-neutral via `equivValueWithMembers_isEquivIntroValue`, so the carrier-aware candidate
STRENGTHENS the content-free flat-equiv candidate. -/
theorem carrierAwareEquivCandidate_toWeakEquivCandidate {scope : Nat}
    {domainCandidate codomainCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : carrierAwareEquivCandidate domainCandidate codomainCandidate term) :
    dataTaitCandidate isEquivIntroValue term := by
  refine ⟨member.1, ?_⟩
  intro normalForm reachesNF nfIsNormal
  rcases member.2 normalForm reachesNF nfIsNormal with isCarrierEquiv | isNeutral
  · exact Or.inl (equivValueWithMembers_isEquivIntroValue isCarrierEquiv)
  · exact Or.inr isNeutral

/-- **A normal `equivIntro` of two carrier-respecting functions is a carrier-aware member.**  An equiv value
`equivIntroValueCell forwardFn backwardFn` with normal carrier-respecting components is a carrier-aware
equivalence member (a structural normal form, strongly normalizing, reducing only to itself — a carrier-aware
`equivIntro`).  The equiv-intro shape the `equivIntro` constructor FT arm produces. -/
theorem carrierAwareEquivCandidate.memberOfNormalEquivIntro {scope : Nat}
    {domainCandidate codomainCandidate : RawTerm scope → Prop} {forwardFn backwardFn : RawTerm scope}
    (cellIsNormal : RawTerm.isStepNormalForm (equivIntroValueCell forwardFn backwardFn))
    (forwardNormal : RawTerm.isStepNormalForm forwardFn)
    (backwardNormal : RawTerm.isStepNormalForm backwardFn)
    (forwardResp : ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate (applicationCell forwardFn argument))
    (backwardResp : ∀ argument : RawTerm scope, codomainCandidate argument →
      domainCandidate (applicationCell backwardFn argument)) :
    carrierAwareEquivCandidate domainCandidate codomainCandidate
      (equivIntroValueCell forwardFn backwardFn) :=
  dataTaitCandidate.memberOfValue cellIsNormal
    ⟨forwardFn, backwardFn, rfl, forwardNormal, backwardNormal, forwardResp, backwardResp⟩

/-- **★ Closed equivalence canonicity (candidate level): a closed carrier-aware equiv member reduces to an
`equivIntro` value.**  Instant from the generic `dataTaitCandidate.closedReducesToValue` followed by the
predicate-level refinement — the model leg the FTGEN-5.5 type dispatch will lift to closed `equivCode`
canonicity. -/
theorem carrierAwareEquivCandidate.closedReducesToEquivIntro
    {domainCandidate codomainCandidate : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : carrierAwareEquivCandidate domainCandidate codomainCandidate term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isEquivIntroValue value ∧
      RawTerm.isStepNormalForm value := by
  obtain ⟨value, chain, valueIsCarrierEquiv, valueNormal⟩ :=
    dataTaitCandidate.closedReducesToValue member
  exact ⟨value, chain, equivValueWithMembers_isEquivIntroValue valueIsCarrierEquiv, valueNormal⟩

/-- **The carrier-aware equivalence predicate is congruent in its carriers.**  Pointwise-equivalent carrier
candidates yield pointwise-equivalent carrier-aware equivalence predicates — each function-respect `∀`-conjunct
transports along the carrier iffs (the domain candidate sits in the forward function's hypothesis and the
backward function's conclusion; the codomain candidate symmetrically — so both legs of each iff are used). -/
theorem equivValueWithMembers_congr {scope : Nat}
    {domainCandidate1 domainCandidate2 codomainCandidate1 codomainCandidate2 : RawTerm scope → Prop}
    (domainIff : PointwiseIff domainCandidate1 domainCandidate2)
    (codomainIff : PointwiseIff codomainCandidate1 codomainCandidate2) :
    PointwiseIff (equivValueWithMembers domainCandidate1 codomainCandidate1)
      (equivValueWithMembers domainCandidate2 codomainCandidate2) := by
  intro term
  constructor
  · rintro ⟨forwardFn, backwardFn, termEq, forwardNormal, backwardNormal, forwardResp, backwardResp⟩
    refine ⟨forwardFn, backwardFn, termEq, forwardNormal, backwardNormal, ?_, ?_⟩
    · intro argument argumentInDomain2
      exact (codomainIff (applicationCell forwardFn argument)).mp
        (forwardResp argument ((domainIff argument).mpr argumentInDomain2))
    · intro argument argumentInCodomain2
      exact (domainIff (applicationCell backwardFn argument)).mp
        (backwardResp argument ((codomainIff argument).mpr argumentInCodomain2))
  · rintro ⟨forwardFn, backwardFn, termEq, forwardNormal, backwardNormal, forwardResp, backwardResp⟩
    refine ⟨forwardFn, backwardFn, termEq, forwardNormal, backwardNormal, ?_, ?_⟩
    · intro argument argumentInDomain1
      exact (codomainIff (applicationCell forwardFn argument)).mpr
        (forwardResp argument ((domainIff argument).mp argumentInDomain1))
    · intro argument argumentInCodomain1
      exact (domainIff (applicationCell backwardFn argument)).mpr
        (backwardResp argument ((codomainIff argument).mp argumentInCodomain1))

/-- **★ The carrier-aware equivalence candidate is congruent in its carriers (the determinism core).**  When
the carrier candidates are pointwise-equivalent, the carrier-aware equivalence candidates are
pointwise-equivalent — the equivalence cousin of `carrierAwarePairCandidate_congr` and exactly the finishing
lemma the table-driven `dataFlatCarrierAware` arm's `deterministic` equivalence case will need, without
`funext`. -/
theorem carrierAwareEquivCandidate_congr {scope : Nat}
    {domainCandidate1 domainCandidate2 codomainCandidate1 codomainCandidate2 : RawTerm scope → Prop}
    (domainIff : PointwiseIff domainCandidate1 domainCandidate2)
    (codomainIff : PointwiseIff codomainCandidate1 codomainCandidate2) :
    PointwiseIff (carrierAwareEquivCandidate domainCandidate1 codomainCandidate1)
      (carrierAwareEquivCandidate domainCandidate2 codomainCandidate2) :=
  dataTaitCandidate_congr (equivValueWithMembers_congr domainIff codomainIff)

end FX1Poly.Core
