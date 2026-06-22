import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate

/-! # FX1Poly/Core/CarrierAwarePairCandidate
    — the carrier-aware product Tait candidate (FTGEN-5.1 substrate, brick 1)

The flat product code's reducibility candidate shipped in `FlatCodeTaitCandidate` is the CONTENT-FREE
`dataTaitCandidate isPairValue`: it tracks only "reduces to a pair value", forgetting whether the pair's
COMPONENTS are themselves reducible members of the carrier types `A`, `B`.  That content-freeness is exactly
the placeholder the denote-keyed `dataFlat` arm of `ReducibleTypeStepDenote` inherits, and it walls the
native fundamental theorem's projection (`fst` / `snd`) eliminator arms: `fst scrutinee ∈ ⟦A⟧` needs the
first component to be a member of `⟦A⟧`, a fact the weak candidate does not record.

This file builds the CARRIER-AWARE replacement at the pure candidate level — the substrate the carrier-
recursive `dataFlat` arm will store and the projection eliminator arms will consume:

  * `pairValueWithMembers firstCandidate secondCandidate` — the carrier-aware pair-value predicate: a pair
    whose normal components satisfy the carrier candidates.
  * `carrierAwarePairCandidate firstCandidate secondCandidate` — `dataTaitCandidate` at that predicate, so
    ALL Girard candidate metatheory (CR1/CR2/CR3, head-expansion closure, member multi-step expansion) is
    inherited instantly and uniformly in the carriers.
  * `pairValueWithMembers_isPairValue` / `carrierAwarePairCandidate_toWeakPairCandidate` — the REFINEMENT:
    every carrier-aware member is a (weak) `dataTaitCandidate isPairValue` member, so the carrier-aware
    candidate STRENGTHENS the content-free flat-product candidate without dropping any of its consumers
    (it directly supplies the `scrutineeMember` premise of `fstDataTaitMember` / `sndDataTaitMember`).
  * `carrierAwarePairCandidate.memberOfNormalPair` — the intro: a normal pair with carrier-member
    components is a carrier-aware member (the data-intro shape the constructor FT arm produces).

## Zero-axiom verification

Every candidate property is an instance of the shipped generic `dataTaitCandidate` bundle at the carrier-
aware value predicate; the refinement drops two conjuncts of an existential.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware pair-value predicate.**  A term is a carrier-aware pair value when it IS a pair
`pairCell first second` whose components are normal forms AND lie in the carrier candidates
`firstCandidate` / `secondCandidate`.  The strengthening of `isPairValue` that records component
reducibility — the content the weak flat-product candidate drops. -/
def pairValueWithMembers {scope : Nat} (firstCandidate secondCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  ∃ first second : RawTerm scope, term = pairCell first second ∧
    RawTerm.isStepNormalForm first ∧ RawTerm.isStepNormalForm second ∧
    firstCandidate first ∧ secondCandidate second

/-- **The carrier-aware product Tait candidate.**  `dataTaitCandidate` at the carrier-aware pair-value
predicate: "strongly normalizing, and every reachable normal form is a carrier-aware pair value or
neutral".  Refines the content-free `dataTaitCandidate isPairValue` (the weak flat-product candidate). -/
def carrierAwarePairCandidate {scope : Nat} (firstCandidate secondCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate (pairValueWithMembers firstCandidate secondCandidate)

/-- **The carrier-aware product candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from
the generic `dataTaitCandidate` bundle, uniformly in the carriers. -/
theorem carrierAwarePairCandidate_isReducibilityCandidate {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (carrierAwarePairCandidate firstCandidate secondCandidate) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The carrier-aware product candidate is head-expansion-closed** — Π-codomain-ready (the FT's
Π-introduction arm property), instant from the generic theorem. -/
theorem carrierAwarePairCandidate_headExpansionClosed {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (carrierAwarePairCandidate firstCandidate secondCandidate) :=
  dataTaitCandidate_headExpansionClosed

/-- **A carrier-aware pair value is a (weak) pair value** — drop the carrier-membership conjuncts.  The
predicate-level half of the refinement. -/
theorem pairValueWithMembers_isPairValue {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (carrierAware : pairValueWithMembers firstCandidate secondCandidate term) :
    isPairValue term := by
  obtain ⟨first, second, termEq, firstNormal, secondNormal, _firstMember, _secondMember⟩ := carrierAware
  exact ⟨first, second, termEq, firstNormal, secondNormal⟩

/-- **★ Refinement: every carrier-aware product member is a (weak) `dataTaitCandidate isPairValue` member.**
Carries each reachable normal form's carrier-aware-pair-or-neutral disjunct down to pair-or-neutral via
`pairValueWithMembers_isPairValue`, so the carrier-aware candidate STRENGTHENS the content-free flat-product
candidate — and directly supplies the `scrutineeMember` premise the projection eliminator arms
(`fstDataTaitMember` / `sndDataTaitMember`) consume. -/
theorem carrierAwarePairCandidate_toWeakPairCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : carrierAwarePairCandidate firstCandidate secondCandidate term) :
    dataTaitCandidate isPairValue term := by
  refine ⟨member.1, ?_⟩
  intro normalForm reachesNF nfIsNormal
  rcases member.2 normalForm reachesNF nfIsNormal with isCarrierPair | isNeutral
  · exact Or.inl (pairValueWithMembers_isPairValue isCarrierPair)
  · exact Or.inr isNeutral

/-- **A normal pair of carrier members is a carrier-aware member.**  A pair value `pairCell first second`
with normal components in the carriers is a carrier-aware product member (it is a structural normal form, so
strongly normalizing, and reduces only to itself — a carrier-aware pair value).  The data-intro shape the
constructor FT arm produces for the dependent pair at carrier-typed components. -/
theorem carrierAwarePairCandidate.memberOfNormalPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {first second : RawTerm scope}
    (pairIsNormal : RawTerm.isStepNormalForm (pairCell first second))
    (firstNormal : RawTerm.isStepNormalForm first) (secondNormal : RawTerm.isStepNormalForm second)
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    carrierAwarePairCandidate firstCandidate secondCandidate (pairCell first second) :=
  dataTaitCandidate.memberOfValue pairIsNormal
    ⟨first, second, rfl, firstNormal, secondNormal, firstMember, secondMember⟩

end FX1Poly.Core
