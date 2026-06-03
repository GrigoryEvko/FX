import FX1Poly.Core.CanonicalFormsCandidate

/-! # FX1Poly/Core/CanonicalFormsWeakHeadExpansion
    — weak-head expansion (backward closure) for the data candidate, in the regime where it HOLDS

`CanonicalFormsCandidate` ships the forward closure (CR2, `closedUnderStep`) and the canonicity payload
(`closedReducesToValue`).  The recursor VALUE-cases (`natElimValueReducibility`, `listElimValueReducibility`)
need the BACKWARD direction — weak-head expansion: a redex inherits membership from its contractum.  This file
supplies it, in the regime where it is actually TRUE.

## The honest scope — why "value-reaching", not unconditional

The data candidate `CanonicalFormsPredicate isValue term := SN term ∧ (IsNeutral term ∨ term ↝* value)` is NOT
weak-head-expansion-closed for an arbitrary member contractum.  When the contractum is NEUTRAL, expansion FAILS:
a redex `r` that weak-head-steps to a neutral `n` is itself NOT neutral (it fired a head redex — a neutral is by
definition stuck), and it does not reduce to a value (it reduces to the stuck `n`).  So neither disjunct holds for
`r`, and `r ∉ CanonicalFormsPredicate isValue`.  This is not a proof gap — it is a true non-closure of this
candidate (the proper Tait candidate that IS unconditionally head-expansion-closed is the bare SN candidate /
the arrow former, `HeadExpansionClosure.lean`; the canonical-forms candidate trades that for canonicity content).

Expansion DOES hold whenever the contractum reduces to a value: `r ↝ contractum ↝* value` gives `r ↝* value`
by `StepStar` transitivity, so `r` is a member via the reduces-to-value disjunct (its SN supplied separately).
This is exactly the regime the closed-canonicity recursor assembly lives in: a closed scrutinee reduces to a
constructor (canonicity), the ι rule fires, and the closed branch contractum itself reduces to a value — so the
recursor cell reaches a value.  These lemmas are that step, packaged for reuse.

## Zero-axiom verification

Each is `StepStar.trans` / `StepStar.trans_compose` into the reduces-to-value disjunct (and, for the
member-shaped form, an `rcases` on the member's disjunct with the neutral branch refuted by hypothesis).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms`
in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **Weak-head expansion into the reduces-to-value disjunct.**  A term that steps to a value-reaching
contractum, and is itself strongly normalizing, is a member of the data candidate: `redexTerm ↝ contractum`
and `contractum ↝* value` compose to `redexTerm ↝* value` (`StepStar.trans`), the reduces-to-value disjunct.
The SN witness for `redexTerm` is supplied directly (the redex's own SN, e.g. the recursor cell's ι-redex SN). -/
theorem CanonicalFormsPredicate.weakHeadExpansionOfValueReaching {scope : Nat}
    {isValue : RawTerm scope → Prop} {redexTerm contractum : RawTerm scope}
    (redexStepsToContractum : Step redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumReachesValue : ∃ value : RawTerm scope, StepStar contractum value ∧ isValue value) :
    CanonicalFormsPredicate isValue redexTerm := by
  obtain ⟨value, contractumToValue, valueIsValue⟩ := contractumReachesValue
  exact ⟨redexStronglyNormalizing,
    Or.inr ⟨value, StepStar.trans redexStepsToContractum contractumToValue, valueIsValue⟩⟩

/-- **Multi-step weak-head expansion into the reduces-to-value disjunct.**  The `StepStar` form of
`weakHeadExpansionOfValueReaching`: a term reducing (by any chain) to a value-reaching contractum, itself SN,
is a member.  The two chains compose by `StepStar.trans_compose`.  This is the reusable shape when the redex
reaches its contractum by several weak-head steps rather than one. -/
theorem CanonicalFormsPredicate.ofStepStarReachingValue {scope : Nat}
    {isValue : RawTerm scope → Prop} {redexTerm contractum : RawTerm scope}
    (redexReachesContractum : StepStar redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumReachesValue : ∃ value : RawTerm scope, StepStar contractum value ∧ isValue value) :
    CanonicalFormsPredicate isValue redexTerm := by
  obtain ⟨value, contractumToValue, valueIsValue⟩ := contractumReachesValue
  exact ⟨redexStronglyNormalizing,
    Or.inr ⟨value, redexReachesContractum.trans_compose contractumToValue, valueIsValue⟩⟩

/-- **Member-shaped weak-head expansion (non-neutral contractum).**  A redex stepping to a member contractum
that is not neutral lifts to a member redex.  The member's "neutral or reduces-to-value" disjunct splits: the
neutral branch is refuted by `contractumNotNeutral`, and the reduces-to-value branch feeds
`weakHeadExpansionOfValueReaching`.  This is the directly-usable form for the recursor value-cases — the ι
contractum (a closed branch member) is non-neutral, so its membership lifts to the recursor cell. -/
theorem CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral {scope : Nat}
    {isValue : RawTerm scope → Prop} {redexTerm contractum : RawTerm scope}
    (redexStepsToContractum : Step redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumMember : CanonicalFormsPredicate isValue contractum)
    (contractumNotNeutral : ¬ IsNeutral contractum) :
    CanonicalFormsPredicate isValue redexTerm := by
  rcases contractumMember.2 with contractumIsNeutral | contractumReachesValue
  · exact (contractumNotNeutral contractumIsNeutral).elim
  · exact CanonicalFormsPredicate.weakHeadExpansionOfValueReaching redexStepsToContractum
      redexStronglyNormalizing contractumReachesValue

end FX1Poly.Core
