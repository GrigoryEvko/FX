import FX1Poly.Typed.BoundedGrownFundamental
import FX1Poly.Typed.BoundExceedsPiDischarge

/-! # FX1Poly/Typed/ClosedBoundedReducibleMember
    — the closed-term bounded-reducibility corollary (BFT-13)

For a CLOSED grown derivation `HasTypeDescPi .empty subject classifier` (empty context, scope 0), there is a bound
at which `subject` is a bound-reducible member of `classifier` under the (unique, vacuous) closing substitution into
scope 1.  This is the corollary that turns the budget-conditional grown fundamental theorem (BFT-12c) into an
UNCONDITIONAL closed-term reducibility fact — the last assembly step before the member→SN bridge (BFT-14) reflects
it to `IsStronglyNormalizing subject` = SN-043.

## The assembly (three shipped pieces)

  1. `BoundExceedsPi.existsBound d` (BFT-12b) supplies a concrete `bound` and budget for the derivation `d`.
  2. `HasTypeDescPi.fundamentalAtBoundedSucc env bound d budget` (BFT-12c) gives `FundamentalConclusionAtBounded\
     Succ env bound .empty subject classifier`, i.e. `∀ {targetScope} (σ : RawTermSubst 0 (targetScope+1)),
     ReducibleEnvAtBounded env bound .empty σ → IsReducibleMemberAtBounded env bound (σ classifier) (σ subject)`.
  3. Instantiate at `targetScope := 0` with the unique closing substitution `Fin.elim0 : RawTermSubst 0 1`
     (`RawTermSubst 0 1 = Fin 0 → RawTerm 1`, so `Fin.elim0` is the only inhabitant) and the vacuous empty-context
     environment witness `ReducibleEnvAtBounded.empty` (`Fin 0` is uninhabited).

The closing substitution lands in scope `0 + 1 = 1` (the +1-motive's scope), so `RawTerm.subst Fin.elim0 subject`
is the canonical weakening of the closed `subject` into scope 1 — exactly the form the scope+1 bounded CR1 expects
(BFT-14 reads SN off it, then reflects through the weakening to the scope-0 `subject`).

## Zero-axiom verification

A composition of three shipped zero-axiom results + `Fin.elim0` (uninhabited-domain function) + `ReducibleEnvAt\
Bounded.empty`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked:
depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The closed-term bounded-reducibility corollary (BFT-13).**  Every closed grown derivation
(`HasTypeDescPi .empty subject classifier`) has a bound at which its `subject` is a bound-reducible member of
`classifier`, under the unique closing substitution `Fin.elim0 : RawTermSubst 0 1` (weakening the closed term into
scope 1).  Composes `BoundExceedsPi.existsBound` (BFT-12b) → `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c) →
the empty-context environment witness.  The unconditional closed-reducibility fact feeding the member→SN bridge
(BFT-14 → SN-043). -/
theorem HasTypeDescPi.closedBoundedReducibleMember {profile : PolyProfile} (env : Nat → Nat)
    {subject classifier : RawTerm 0}
    (d : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ bound : Nat,
      IsReducibleMemberAtBounded env bound
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) classifier)
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) := by
  obtain ⟨bound, budget⟩ := BoundExceedsPi.existsBound (env := env) d
  refine ⟨bound, ?_⟩
  exact HasTypeDescPi.fundamentalAtBoundedSucc env bound d budget
    (targetScope := 0) (Fin.elim0 : RawTermSubst 0 1)
    (ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1))

end FX1Poly.Typed
