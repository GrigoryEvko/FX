import FX1Poly.Typed.Dimensions.Parametricity.KernelBinaryParametricity
import FX1Poly.Typed.Cell.CellConstructors

/-! # FX1Poly/Typed/BridgeRelationalScone — the relational Bridge scone (NATIVE-57)

The MODEL side of internal parametricity.  The OP1-INT verdict (`KernelParamInternalVerdict`)
certified that the `gen_param` SUBSTRATE is present and ADMITS — but admission is not yet a
usable free theorem.  This file gives the bridge former its parametric CONTENT: the reducibility
scone of `Bridge A a b` (`bridgeTypeCell`) CARRIES the carrier type `A`'s binary candidate (its
relation), and a bridge inhabitant `p : Bridge A a b` internally WITNESSES that the endpoints
`a`, `b` are related in that relation.  This is the relational interpretation of Bernardy–Coquand–
Moulin / Cavallo–Harper, expressed against the shipped binary logical relation
(`KernelBinaryParametricity`) rather than a syntactic `Gel` former (which the kernel deliberately
does NOT carry — internalizing the relation in the SCONE avoids the generator cascade).

  * `bridgeRelationalCandidate` — ★ the relation-carrying member predicate: a bridge proof is a
    member exactly when it is strongly normalizing AND the endpoints are `carrierRelation`-related.
    The candidate is PARAMETERIZED by (carries) the carrier's binary candidate — that is the whole
    point of "relational scone".  Membership is proof-irrelevant in the proof term (the standard
    parametricity choice at bridge types, mirroring the binary `neutral` arm's SN-product) and
    LOAD-BEARING in the endpoint relation.
  * `bridgeRelationalCandidate_extractsRelation` — ★ the internalized free theorem: from any
    member, recover `carrierRelation left right`.  An inhabitant of the bridge type IS evidence of
    endpoint-relatedness — exactly the content `KernelAbstractionTheorem` extracts externally, now
    living in the type.
  * `bridgeRelationalCandidate.intro` / `_memberIsStronglyNormalizing` — the introduction and the
    SN projection (the candidate is a sub-predicate of strong normalization, so the bridge type is
    SN-sound, a reducibility-candidate prerequisite).
  * `bridgeRelationalCandidate_congrInCarrier` — relation-carrying congruence: the scone depends on
    the carrier relation only pointwise at the endpoints (`BinaryPointwiseIff`-stable), the
    `funext`-free discipline the binary model uses throughout.
  * ★ TEETH (the relation does real work): `bridgeRelationalScone_inhabitedAtRelatedEndpoints`
    populates the scone over the related pair `(firstWitnessPairValue, firstWitnessPairValue)`,
    while `bridgeRelationalScone_emptyAtUnrelatedEndpoints` shows the scone over the UNRELATED pair
    `(firstWitnessPairValue, secondWitnessPairValue)` is member-free — even though BOTH endpoints
    are unary data-Tait members.  A bridge cannot span endpoints the carrier relation refuses; the
    relational interpretation is not decorative.

Honest scope: this is the bridge type's member candidate and its teeth.  Wiring the candidate into
`ReducibleTypeStepBounded` as a bridge ARM (so `bridgeTypeCell` becomes a reducible TYPE whose
member predicate IS `bridgeRelationalCandidate`) and the reflexive identity-path membership travel
with NATIVE-58; the affine premise's semantic role (why duplication collapses the relation) is
NATIVE-59.

Zero-axiom; gated in `FX1PolyAudit/AuditBridgeRelationalScone.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## The relation-carrying member predicate -/

/-- ★ **The relational Bridge scone candidate.**  The member predicate the reducibility scone of
`Bridge A a b` carries: a bridge proof is a member exactly when it is strongly normalizing and the
endpoints `left`, `right` are related in the carrier type `A`'s binary candidate.  The candidate is
parameterized by (CARRIES) `carrierRelation`, so the relational content of the bridge type lives in
its scone — the semantic analogue of a `Gel`/extent type without a syntactic former. -/
def bridgeRelationalCandidate {scope : Nat}
    (carrierRelation : BinaryCandidate scope) (left right : RawTerm scope) :
    RawTerm scope → Prop :=
  fun bridgeProof => IsStronglyNormalizing bridgeProof ∧ carrierRelation left right

/-- **Introduction.**  A strongly-normalizing proof over a related endpoint pair is a member. -/
theorem bridgeRelationalCandidate.intro {scope : Nat}
    {carrierRelation : BinaryCandidate scope} {left right bridgeProof : RawTerm scope}
    (proofIsStronglyNormalizing : IsStronglyNormalizing bridgeProof)
    (endpointsRelated : carrierRelation left right) :
    bridgeRelationalCandidate carrierRelation left right bridgeProof :=
  ⟨proofIsStronglyNormalizing, endpointsRelated⟩

/-- ★ **The internalized free theorem.**  Every member of the bridge scone yields endpoint
relatedness: an inhabitant of `Bridge A a b` IS evidence that `a` and `b` are related in `A`'s
binary candidate — the abstraction theorem's content, now extracted INSIDE the type theory. -/
theorem bridgeRelationalCandidate_extractsRelation {scope : Nat}
    {carrierRelation : BinaryCandidate scope} {left right bridgeProof : RawTerm scope}
    (member : bridgeRelationalCandidate carrierRelation left right bridgeProof) :
    carrierRelation left right :=
  member.2

/-- **SN soundness.**  Bridge members are strongly normalizing — the reducibility-candidate
prerequisite (CR1) for the bridge type. -/
theorem bridgeRelationalCandidate_memberIsStronglyNormalizing {scope : Nat}
    {carrierRelation : BinaryCandidate scope} {left right bridgeProof : RawTerm scope}
    (member : bridgeRelationalCandidate carrierRelation left right bridgeProof) :
    IsStronglyNormalizing bridgeProof :=
  member.1

/-- **Relation-carrying congruence.**  The scone depends on the carrier relation only through its
value at the endpoints; pointwise-equivalent carrier relations give the same bridge scone
(`funext`-free, the binary model's `BinaryPointwiseIff` discipline). -/
theorem bridgeRelationalCandidate_congrInCarrier {scope : Nat}
    {carrierRelationA carrierRelationB : BinaryCandidate scope} {left right bridgeProof : RawTerm scope}
    (carriersAgree : BinaryPointwiseIff carrierRelationA carrierRelationB) :
    bridgeRelationalCandidate carrierRelationA left right bridgeProof ↔
      bridgeRelationalCandidate carrierRelationB left right bridgeProof :=
  ⟨fun member => ⟨member.1, (carriersAgree left right).mp member.2⟩,
   fun member => ⟨member.1, (carriersAgree left right).mpr member.2⟩⟩

/-! ## ★ TEETH: the carrier relation is load-bearing -/

/-- ★ **Inhabited at a related endpoint pair.**  Over `(firstWitnessPairValue,
firstWitnessPairValue)` — which the binary data candidate relates to itself
(`binaryPairCandidate_relatesSelf`) — the bridge scone is inhabited (any SN proof works; here the
normal form `emptyTypeCell` is the witness). -/
theorem bridgeRelationalScone_inhabitedAtRelatedEndpoints :
    bridgeRelationalCandidate (binaryDataCandidate isPairValue)
      firstWitnessPairValue firstWitnessPairValue emptyTypeCell :=
  bridgeRelationalCandidate.intro
    (IsStronglyNormalizing.ofIsStepNormalForm rfl)
    binaryPairCandidate_relatesSelf

/-- ★ **Member-free at an unrelated endpoint pair.**  Over `(firstWitnessPairValue,
secondWitnessPairValue)` — which the binary data candidate REFUSES
(`binaryPairCandidate_discriminates`), even though both are unary data-Tait members — the bridge
scone has NO members, whatever the proof term.  A bridge cannot span endpoints the carrier relation
does not relate: the relational interpretation is load-bearing, not decorative. -/
theorem bridgeRelationalScone_emptyAtUnrelatedEndpoints :
    ¬ ∃ bridgeProof : RawTerm 0,
        bridgeRelationalCandidate (binaryDataCandidate isPairValue)
          firstWitnessPairValue secondWitnessPairValue bridgeProof := by
  intro witnessed
  obtain ⟨_bridgeProof, member⟩ := witnessed
  exact binaryPairCandidate_discriminates
    (bridgeRelationalCandidate_extractsRelation member)

/-- The teeth bundled: the SAME carrier relation populates the scone at the related pair and empties
it at the unrelated pair — the bridge scone tracks the carrier relation faithfully. -/
theorem bridgeRelationalScone_tracksCarrierRelation :
    bridgeRelationalCandidate (binaryDataCandidate isPairValue)
        firstWitnessPairValue firstWitnessPairValue emptyTypeCell
      ∧ ¬ ∃ bridgeProof : RawTerm 0,
          bridgeRelationalCandidate (binaryDataCandidate isPairValue)
            firstWitnessPairValue secondWitnessPairValue bridgeProof :=
  ⟨bridgeRelationalScone_inhabitedAtRelatedEndpoints,
   bridgeRelationalScone_emptyAtUnrelatedEndpoints⟩

end FX1Poly.Typed
