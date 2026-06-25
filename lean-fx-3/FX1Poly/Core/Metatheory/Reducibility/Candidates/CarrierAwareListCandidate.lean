import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareOptionCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate

/-! # FX1Poly/Core/CarrierAwareListCandidate
    — the carrier-aware list Tait candidate (GATE1-SWAP4 substrate, the RECURSIVE unary carrier-aware row)

The flat list code's content-free candidate (`dataTaitCandidate IsListStructured`) tracks only the structural
spine ("`nil`, a stuck neutral, or `cons` of a NORMAL head onto a structured tail"), forgetting whether each
`cons` HEAD is itself a reducible member of the carrier type `A`.  That content-freeness walls the native
fundamental theorem's `listElim` eliminator arm: dispatching on `cons head tail` needs `head ∈ ⟦A⟧` to type the
cons-branch's first Π argument, a fact the weak candidate does not record — exactly the gap the carrier-aware
option candidate (`CarrierAwareOptionCandidate`) fills for `optionMatch`, now lifted to the RECURSIVE list spine.

This file builds the carrier-aware list candidate — the list twin of `carrierAwareOptionCandidate`, but RECURSIVE
because `cons` carries a HEAD of the element type `A` AND a TAIL of the list type `List A` (unlike option's
nullary `none` / unary `some`).  It is a `dataTaitCandidate` (the SAME generic Tait bundle the option/either rows
use) at a carrier-aware list-value predicate, so ALL Girard candidate metatheory (CR1/CR2/CR3, head-expansion
closure, member multi-step expansion) is inherited instantly and uniformly in the carrier:

  * `listValueWithMember carrierCandidate` — the carrier-aware list-value predicate: `IsListStructured` with the
    cons head additionally a carrier member.  A RECURSIVE inductive (the `cons` tail is recursively a
    carrier-aware list value), the carrier-bearing strengthening of `IsListStructured`.
  * `carrierAwareListCandidate carrierCandidate` — `dataTaitCandidate` at that predicate, so the full candidate
    bundle is inherited.
  * `listValueWithMember_isListStructured` / `carrierAwareListCandidate_toWeakListCandidate` — the REFINEMENT:
    every carrier-aware member is a (weak) `dataTaitCandidate IsListStructured` member, so the carrier-aware
    candidate STRENGTHENS the content-free flat-list candidate without dropping any of its consumers.
  * `carrierAwareListCandidate.memberOfNormalNil` / `.memberOfNormalCons` — the intros the `nil`/`cons`
    constructor FT arms produce.
  * `carrierAwareListCandidate_congr` — the determinism core: a pointwise-equivalent carrier yields a
    pointwise-equivalent list candidate (the carrier swaps COVARIANTLY at every cons head, structurally), without
    `funext`.

## Zero-axiom verification

Every candidate property is an instance of the shipped generic `dataTaitCandidate` bundle at the carrier-aware
list predicate; the refinement and congruence are structural inductions on `listValueWithMember` (the cons head's
carrier conjunct dropped / swapped, the recursive tail by the induction hypothesis).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware list-value predicate.**  `IsListStructured` strengthened so each `cons` HEAD is a
carrier member: `nil`; a NORMAL neutral (the open-scope stuck base case); or `cons` of a NORMAL head that lies in
`carrierCandidate` onto a recursively carrier-aware tail.  The carrier-bearing twin of `IsListStructured` — the
content (head reducibility) the weak structured candidate drops.  RECURSIVE in the tail, the list analogue of
`optionValueWithMember`'s single `some` payload conjunct. -/
inductive listValueWithMember {scope : Nat} (carrierCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop where
  /-- `nil` is a carrier-aware list value. -/
  | nil : listValueWithMember carrierCandidate listNilCell
  /-- A NORMAL neutral is a carrier-aware list value — the open-scope stuck base case. -/
  | neutralNormal {neutralTerm : RawTerm scope} (isNeutral : IsNeutral neutralTerm)
      (isNormal : RawTerm.isStepNormalForm neutralTerm) :
      listValueWithMember carrierCandidate neutralTerm
  /-- `cons` of a NORMAL carrier-member head onto a recursively carrier-aware tail is a carrier-aware list
  value — the cons spine recursion, carrying the head's carrier membership. -/
  | cons {head tail : RawTerm scope} (headNormal : RawTerm.isStepNormalForm head)
      (headMember : carrierCandidate head)
      (tailValue : listValueWithMember carrierCandidate tail) :
      listValueWithMember carrierCandidate (listConsCell head tail)

/-- **A carrier-aware list value is a (weak) structured list value** — drop the head's carrier-membership
conjunct from every `cons`, recursing structurally on the tail.  The predicate-level half of the refinement, the
list twin of `optionValueWithMember_isOptionValue`. -/
theorem listValueWithMember_isListStructured {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (carrierAware : listValueWithMember carrierCandidate term) :
    IsListStructured term := by
  induction carrierAware with
  | nil => exact IsListStructured.nil
  | neutralNormal isNeutral isNormal => exact IsListStructured.neutralNormal isNeutral isNormal
  | cons headNormal _headMember _tailValue tailStructured =>
      exact IsListStructured.cons headNormal tailStructured

/-- **The carrier-aware list Tait candidate.**  `dataTaitCandidate` at the carrier-aware list-value predicate:
"strongly normalizing, and every reachable normal form is a carrier-aware list value or neutral".  Refines the
content-free `dataTaitCandidate IsListStructured`. -/
def carrierAwareListCandidate {scope : Nat} (carrierCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate (listValueWithMember carrierCandidate)

/-- **The carrier-aware list candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from the
generic `dataTaitCandidate` bundle, uniformly in the carrier. -/
theorem carrierAwareListCandidate_isReducibilityCandidate {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (carrierAwareListCandidate carrierCandidate) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The carrier-aware list candidate is head-expansion-closed** — Π-codomain-ready, instant from the generic
theorem. -/
theorem carrierAwareListCandidate_headExpansionClosed {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (carrierAwareListCandidate carrierCandidate) :=
  dataTaitCandidate_headExpansionClosed

/-- **★ Refinement: every carrier-aware list member is a (weak) `dataTaitCandidate IsListStructured` member.**
Carries each reachable normal form's carrier-aware-list-value-or-neutral disjunct down to structured-or-neutral
via `listValueWithMember_isListStructured`, so the carrier-aware candidate STRENGTHENS the content-free
flat-list candidate — and directly supplies the `scrutineeMember` premise the closed-list canonicity extraction
consumes. -/
theorem carrierAwareListCandidate_toWeakListCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : carrierAwareListCandidate carrierCandidate term) :
    dataTaitCandidate IsListStructured term := by
  refine ⟨member.1, ?_⟩
  intro normalForm reachesNF nfIsNormal
  rcases member.2 normalForm reachesNF nfIsNormal with isCarrierList | isNeutral
  · exact Or.inl (listValueWithMember_isListStructured isCarrierList)
  · exact Or.inr isNeutral

/-- **The `nil` cell is a carrier-aware list member.**  A structural normal form reducing only to itself — a
carrier-aware list value.  The data-intro shape the `nil` constructor FT arm produces. -/
theorem carrierAwareListCandidate.memberOfNormalNil {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (cellIsNormal : RawTerm.isStepNormalForm (listNilCell (scope := scope))) :
    carrierAwareListCandidate carrierCandidate listNilCell :=
  dataTaitCandidate.memberOfValue cellIsNormal listValueWithMember.nil

/-- **A normal `cons` of a carrier-member head onto a carrier-aware tail is a carrier-aware list member.**  The
data-intro shape the `cons` constructor FT arm produces — head normal and in the carrier, tail a carrier-aware
list value. -/
theorem carrierAwareListCandidate.memberOfNormalCons {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {head tail : RawTerm scope}
    (cellIsNormal : RawTerm.isStepNormalForm (listConsCell head tail))
    (headNormal : RawTerm.isStepNormalForm head) (headMember : carrierCandidate head)
    (tailValue : listValueWithMember carrierCandidate tail) :
    carrierAwareListCandidate carrierCandidate (listConsCell head tail) :=
  dataTaitCandidate.memberOfValue cellIsNormal
    (listValueWithMember.cons headNormal headMember tailValue)

/-- **★ General carrier-aware list cons introduction: `cons` of a reducible head onto a carrier-aware tail is a
carrier-aware member.**  The recursive twin of `carrierAwareOptionCandidate.memberOfReducibleSome`: the head need
only be a reducible carrier member (SN by CR1, reduction-closed by CR2), the tail a carrier-aware list member; the
`cons` cell is SN (`listCons_isStronglyNormalizing_of_head_tail`), and every reachable normal form decomposes
(`stepStar_under_binaryCell`) into `cons headAfter tailAfter` for reachable normal forms — the head's still in the
carrier (CR2 along the head chain), the tail's classified as a carrier-aware list value or a NORMAL neutral (both
`listValueWithMember` arms), so the `cons` is a carrier-aware list value.  The intro the `listCons` constructor FT
row produces post gate-1 swap 4. -/
theorem carrierAwareListCandidate.memberOfReducibleCons {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierCandidateIsCandidate : IsReducibilityCandidate carrierCandidate)
    {head tail : RawTerm scope} (headMember : carrierCandidate head)
    (tailMember : carrierAwareListCandidate carrierCandidate tail) :
    carrierAwareListCandidate carrierCandidate (listConsCell head tail) := by
  refine ⟨listCons_isStronglyNormalizing_of_head_tail
      (carrierCandidateIsCandidate.stronglyNormalizing headMember) tailMember.1, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨headAfter, tailAfter, targetEq, headChain, tailChain⟩ :=
    stepStar_under_binaryCell listConsCell Step.from_listCons reaches head tail rfl
  subst targetEq
  have headAfterNormal : RawTerm.isStepNormalForm headAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact listBoolConjLeft folded
  have tailAfterNormal : RawTerm.isStepNormalForm tailAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact listBoolConjLeft (listBoolConjRight folded)
  have headAfterMember : carrierCandidate headAfter :=
    carrierCandidateIsCandidate.closedUnderStepStar headChain headMember
  rcases tailMember.2 tailAfter tailChain tailAfterNormal with tailIsCarrierList | tailIsNeutral
  · exact Or.inl (listValueWithMember.cons headAfterNormal headAfterMember tailIsCarrierList)
  · exact Or.inl (listValueWithMember.cons headAfterNormal headAfterMember
      (listValueWithMember.neutralNormal tailIsNeutral tailAfterNormal))

/-- **The carrier-aware list-value predicate is congruent in its carrier.**  A pointwise-equivalent carrier
candidate yields a pointwise-equivalent carrier-aware list predicate — every `cons` head's carrier membership
swaps under the carrier iff, the structural spine and head-normality conjuncts untouched, recursing on the
tail. -/
theorem listValueWithMember_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (listValueWithMember carrierCandidate1) (listValueWithMember carrierCandidate2) := by
  intro term
  constructor
  · intro value
    induction value with
    | nil => exact listValueWithMember.nil
    | neutralNormal isNeutral isNormal => exact listValueWithMember.neutralNormal isNeutral isNormal
    | cons headNormal headMember _tailValue tailValueIff =>
        exact listValueWithMember.cons headNormal ((carrierIff _).mp headMember) tailValueIff
  · intro value
    induction value with
    | nil => exact listValueWithMember.nil
    | neutralNormal isNeutral isNormal => exact listValueWithMember.neutralNormal isNeutral isNormal
    | cons headNormal headMember _tailValue tailValueIff =>
        exact listValueWithMember.cons headNormal ((carrierIff _).mpr headMember) tailValueIff

/-- **★ The carrier-aware list candidate is congruent in its carrier (the determinism core).**  When the carrier
candidate is pointwise-equivalent, the carrier-aware list candidates are pointwise-equivalent — the list twin of
`carrierAwareOptionCandidate_congr`, the finishing lemma the arity-generic carrier-aware arm's `deterministic`
list case needs, without `funext`. -/
theorem carrierAwareListCandidate_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (carrierAwareListCandidate carrierCandidate1)
      (carrierAwareListCandidate carrierCandidate2) :=
  dataTaitCandidate_congr (listValueWithMember_congr carrierIff)

end FX1Poly.Core
