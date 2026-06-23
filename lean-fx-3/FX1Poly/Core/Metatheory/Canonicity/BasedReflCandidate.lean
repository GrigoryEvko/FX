import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Rewriting.Confluence.RawConfluence

/-! # FX1Poly/Core/BasedReflCandidate
    — the BASED (endpoint-aware) identity reducibility candidate, for genuine path-induction J

The content-free identity candidate `dataTaitCandidate isReflValue` (`ReflCanonicalFormsCandidate`,
DEP-ID-MODEL) records only "the witness is `refl w` with `w` a structural normal form" — it forgets the
endpoint.  That is enough for the IDENTITY-TYPE formation/introduction reducibility, but NOT for the genuine
DEPENDENT eliminator `idJ` (Martin-Löf path induction): when `idJ`'s witness reduces to `refl w`, the
dependent output `C endpoint witness` must be reclassified from the base case's declared type
`C endpoint (refl endpoint)`, which needs `Conv w endpoint` (the reflected point convertible to the type's
endpoint).  The content-free candidate cannot supply that — `idJ` is the UNIQUE eliminator whose
payload-bearing branch (the base case) is not a function of its payload, so unlike every other eliminator it
cannot adapt to the reached value.

`isReflValueAt endpoint` is the BASED value predicate: `refl w` with `w` normal AND `Conv w endpoint`.  The
candidate `dataTaitCandidate (isReflValueAt endpoint)` is the identity type's reducibility content with the
endpoint tracked.  Because `dataTaitCandidate` is generic over its value predicate, the based candidate
inherits CR1/CR2/CR3, head-expansion-closure, and member extraction for free
(`dataTaitCandidate_isReducibilityCandidate` and friends apply verbatim) — the value predicate is only ever
evaluated at REACHABLE NORMAL FORMS, so its endpoint conjunct never enters the candidate-law proofs.

The reduction-stability that genuine `idJ` needs rides `Conv` being an UNCONDITIONAL equivalence relation
(`Conv.trans` via the table-route global Church-Rosser `StepStar.rawConfluence`, RawConfluence.lean) — no
strong-normalization or confluence side-condition is threaded through the discharge.

## Zero-axiom verification

`reflDataTaitMemberAt` mirrors the content-free `reflDataTaitMember` (the `Step.from_refl` /
`refl_isStronglyNormalizing_of_witness` / `stepStar_under_unaryCell` recipe) and threads the endpoint
conjunct via `Conv.fromStepStar` + `Conv.sym` + `Conv.trans` (all axiom-free; `trans` discharged by
`StepStar.rawConfluence`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The based refl value predicate.**  A term is an identity value AT `endpoint` when it is `refl witness`
with `witness` a structural normal form AND `witness` convertible to `endpoint` (the reflected point matches
the identity type's endpoint up to conversion).  The endpoint-aware refinement of `isReflValue`: every
`isReflValueAt endpoint` value is an `isReflValue` value, the converse fails (a `refl w` with `w` not
convertible to `endpoint` is `isReflValue` but not `isReflValueAt endpoint`). -/
def isReflValueAt {scope : Nat} (endpoint : RawTerm scope) (term : RawTerm scope) : Prop :=
  ∃ witness : RawTerm scope,
    term = reflCell witness ∧ RawTerm.isStepNormalForm witness ∧ Conv witness endpoint

/-- **A based refl value drops to the content-free predicate.**  Forgetting the endpoint conjunct, an
`isReflValueAt endpoint` value is an `isReflValue` value — the easy inclusion confirming the based candidate
is a refinement of the content-free one. -/
theorem isReflValue_ofIsReflValueAt {scope : Nat} {endpoint term : RawTerm scope}
    (valueIsReflAt : isReflValueAt endpoint term) : isReflValue term := by
  obtain ⟨witness, termEq, witnessNormal, _witnessConvEndpoint⟩ := valueIsReflAt
  exact ⟨witness, termEq, witnessNormal⟩

/-- **★ A `refl` of a witness convertible to the endpoint is a based-candidate member.**  The endpoint-aware
companion of `reflDataTaitMember`: a `refl witness` cell, with `witness` strongly normalizing and convertible
to `endpoint`, is a member of `dataTaitCandidate (isReflValueAt endpoint)`.  The reflexivity-introduction
reducibility for the BASED identity candidate — the member the genuine dependent `idJ` bridge consumes (at
`endpoint := witness`, the conversion is `Conv.refl`; the general endpoint rides `Conv.trans`).

The cell is strongly normalizing (`refl_isStronglyNormalizing_of_witness`), and any reachable normal form is
`refl witnessAfter` for a normal `witnessAfter` the original witness reduces to (`stepStar_under_unaryCell`);
`witnessAfter` is then convertible to `endpoint` by chaining the reduction conversion (reversed) with the
hypothesis — so the normal form is an `isReflValueAt endpoint` value. -/
theorem reflDataTaitMemberAt {scope : Nat} {endpoint witness : RawTerm scope}
    (witnessStronglyNormalizing : IsStronglyNormalizing witness)
    (witnessConvEndpoint : Conv witness endpoint) :
    dataTaitCandidate (isReflValueAt endpoint) (reflCell witness) := by
  refine ⟨refl_isStronglyNormalizing_of_witness witnessStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨witnessAfter, targetEq, witnessChain⟩ :=
    stepStar_under_unaryCell reflCell Step.from_refl reaches witness rfl
  subst targetEq
  have witnessAfterNormal : RawTerm.isStepNormalForm witnessAfter := by
    have folded : (RawTerm.isStepNormalFormBool witnessAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  exact Or.inl ⟨witnessAfter, rfl, witnessAfterNormal,
    ((Conv.fromStepStar witnessChain).sym).trans witnessConvEndpoint⟩

/-- **The two-endpoint based refl value predicate.**  A term is an identity value BETWEEN `left` and `right`
when it is `refl witness` with `witness` a structural normal form AND convertible to BOTH endpoints.  The
predicate the genuine `idJ` reducibility arm pins a GENERAL identity code `Id(A, left, right)` to: when `left`
and `right` are convertible (in particular `left = right`, the `idJ` witness type `Id A endpoint endpoint`) a
`refl witness` with `witness` convertible to them is a member; when `left` and `right` are NOT convertible no
`witness` can be convertible to both (that would force `Conv left right`), so the value predicate is uninhabited
and the candidate collapses to the neutrals — exactly right, since a non-reflexive identity code has no
constructor inhabitant. -/
def isReflValueBetween {scope : Nat} (left right : RawTerm scope) (term : RawTerm scope) : Prop :=
  ∃ witness : RawTerm scope,
    term = reflCell witness ∧ RawTerm.isStepNormalForm witness ∧
      Conv witness left ∧ Conv witness right

/-- **A two-endpoint based refl value drops to the content-free predicate.**  Forgetting both endpoint
conjuncts, an `isReflValueBetween left right` value is an `isReflValue` value — the inclusion the genuine `idJ`
bridge composes with to feed the content-free `idJDependentReducibleMember` trichotomy while keeping the
endpoint conversions in hand. -/
theorem isReflValue_ofIsReflValueBetween {scope : Nat} {left right term : RawTerm scope}
    (valueIsReflBetween : isReflValueBetween left right term) : isReflValue term := by
  obtain ⟨witness, termEq, witnessNormal, _convLeft, _convRight⟩ := valueIsReflBetween
  exact ⟨witness, termEq, witnessNormal⟩

/-- **★ A `refl` of a witness convertible to both endpoints is a two-endpoint based-candidate member.**  The
general-endpoint companion of `reflDataTaitMemberAt`: a `refl witness` cell, with `witness` strongly normalizing
and convertible to both `left` and `right`, is a member of `dataTaitCandidate (isReflValueBetween left right)`.
The reflexivity-introduction reducibility for the GENERAL identity candidate — the member the re-pinned refl
introduction produces (at `left := right := witness`, both conversions are `Conv.refl`).  Each reachable normal
form `refl witnessAfter` carries the two endpoint conversions by chaining the (reversed) reduction conversion
with the hypotheses. -/
theorem reflDataTaitMemberBetween {scope : Nat} {left right witness : RawTerm scope}
    (witnessStronglyNormalizing : IsStronglyNormalizing witness)
    (witnessConvLeft : Conv witness left) (witnessConvRight : Conv witness right) :
    dataTaitCandidate (isReflValueBetween left right) (reflCell witness) := by
  refine ⟨refl_isStronglyNormalizing_of_witness witnessStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨witnessAfter, targetEq, witnessChain⟩ :=
    stepStar_under_unaryCell reflCell Step.from_refl reaches witness rfl
  subst targetEq
  have witnessAfterNormal : RawTerm.isStepNormalForm witnessAfter := by
    have folded : (RawTerm.isStepNormalFormBool witnessAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  exact Or.inl ⟨witnessAfter, rfl, witnessAfterNormal,
    ((Conv.fromStepStar witnessChain).sym).trans witnessConvLeft,
    ((Conv.fromStepStar witnessChain).sym).trans witnessConvRight⟩

end FX1Poly.Core
