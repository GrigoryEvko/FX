import FX1Poly.Typed.ClosedBoundedReducibleMember
import FX1Poly.Core.StronglyNormalizingSubst

/-! # FX1Poly/Typed/ClosedStronglyNormalizing
    — SN-for-well-typed, closed case (BFT-14): every closed well-typed grown term is strongly normalizing

`HasTypeDescPi.closedStronglyNormalizing`: for a closed grown derivation `HasTypeDescPi .empty subject classifier`,
`subject` is strongly normalizing — UNCONDITIONALLY, zero-axiom.  This is SN-043 for the closed fragment (the
empty-context case of `HasTypeDescPi Γ t T → IsStronglyNormalizing t`), and the capstone of the bounded
reducibility route (BFT-1..14): the budget-discharged grown fundamental theorem applied at the empty context, with
its reducible member reflected through the scope+1 CR1 and the closing substitution.

## The bridge (member → SN → reflect)

Two shipped steps compose on top of the closed-member corollary (BFT-13):

  1. `stronglyNormalizing_of_memberAtBoundedSucc member` — the scope+1 bounded CR1: a bound-reducible member of any
     type is strongly normalizing (its candidate is an unconditional reducibility candidate).  Applied to BFT-13's
     member, this gives `IsStronglyNormalizing (RawTerm.subst Fin.elim0 subject)` at scope 1.
  2. `StepStar.stronglyNormalizing_of_subst` — SN reflects through ANY substitution (`Step.subst` makes `subst σ` a
     step-preserving map, so accessibility pulls back along it).  Reflecting the scope-1 SN of the weakening
     `subst Fin.elim0 subject` gives `IsStronglyNormalizing subject` at scope 0.

The `env` parameter of the closed member is irrelevant to SN, so it is instantiated to `fun _ => 0`.

## Scope: closed (Γ = .empty)

This is the closed case of SN-043.  The arbitrary-context statement `HasTypeDescPi Γ t T → IsStronglyNormalizing t`
additionally requires a closing substitution sending each context variable to a reducible (neutral) member — the
open-term extension of this bridge — and is tracked separately.  The closed case is exactly what closed-term
canonicity (SN-047/048/049) and consistency (SN-050) consume.

## Zero-axiom verification

A three-step composition of shipped zero-axiom results (`closedBoundedReducibleMember` +
`stronglyNormalizing_of_memberAtBoundedSucc` + `StepStar.stronglyNormalizing_of_subst`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **SN-for-well-typed, closed case (BFT-14 / SN-043-closed).**  Every closed grown derivation
(`HasTypeDescPi .empty subject classifier`) has a strongly-normalizing `subject`, unconditionally.  Composes the
closed-member corollary (BFT-13) with the scope+1 bounded CR1 (`stronglyNormalizing_of_memberAtBoundedSucc`) and
SN-reflection through the closing substitution (`StepStar.stronglyNormalizing_of_subst`).  The capstone of the
bounded reducibility route for closed terms. -/
theorem HasTypeDescPi.closedStronglyNormalizing {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (d : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨bound, member⟩ := HasTypeDescPi.closedBoundedReducibleMember (fun _ => 0) d
  exact StepStar.stronglyNormalizing_of_subst (Fin.elim0 : RawTermSubst 0 1) subject
    (stronglyNormalizing_of_memberAtBoundedSucc member)

end FX1Poly.Typed
