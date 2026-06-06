import FX1Poly.Typed.HasTypeDescPiValidity
import FX1Poly.Typed.WfContextDecidableConv

/-! # FX1Poly/Typed/HasTypeDescPiCheckOfInferred
    — the "check against a known-type target" reduction (the COMPARE half of the bidirectional checker, SN-052)

Decidable typed CHECKING for the grown engine `HasTypeDescPi` must be BIDIRECTIONAL — typing is not unique up
to `Conv` for a bare Curry-style λ (see `HasTypeDescPiTypingNonUnique`), so the checker INFERS at
elimination/variable positions and CHECKS at introduction (λ) positions.  This file ships the load-bearing
COMPARE step shared by the infer-positions: once a subject's type has been synthesized (`inferred`) and the
target is known to be a type (`targetTyped : T : Type`), checking `subject : T` reduces to deciding
`Conv inferredType T` — `isTrue` via the grown `conv` rule, `isFalse` via the subject's per-term uniqueness.

## Why the typing witnesses are explicit (not the `IsTypeDesc` existential)

A `Decidable _` is DATA; it cannot large-eliminate the `Prop`-valued `IsTypeDescPi` existential to recover
the universe-typing witnesses the `Conv` decider needs.  So both `inferred`'s classifier-typing and the
target's universe-typing are threaded EXPLICITLY as arguments — exactly the derivations the inference half
carries (the inference returns `Σ`-packaged data, and the "target is a type" sub-decision yields its witness
as data).  This keeps the combinator constructive and decoupled from the `Prop`-valued validity.

## The uniqueness hypothesis

`uniqueAtSubject` (every type the subject receives is `Conv` to `inferredType`) is the completeness ingredient
of the `isFalse` branch.  It HOLDS for non-λ subjects (var / app / formation cells — whose type is unique up
to `Conv`) and FAILS for bare λ (hence the bidirectional split).  Taking it as a hypothesis makes this
combinator the honest COMPARE step for exactly the infer-mode positions; the λ CHECK-mode position is handled
separately (normalize the given target to a Π-head and recurse on the body).

## Zero-axiom verification

A `match` on `Conv.decidableOfWellTypedInWfContextDesc` (SN-051, the unconditional typed-Conv decider) + the grown
`HasTypeDescPi.conv` rule (`isTrue`) + the `uniqueAtSubject` contradiction (`isFalse`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Decidable checking against a known-type target, given inference + per-subject uniqueness.**  The
COMPARE step of the bidirectional checker: `subject : targetType` is decided by `Conv inferredType targetType`
(both well-typed, so the SN-051 decider applies) — `isTrue` re-types `subject` to `targetType` through the
grown `conv` rule; `isFalse` refutes via `uniqueAtSubject` (any type the subject has is `Conv` to
`inferredType`, contradicting non-convertibility).  Sound AND complete for any subject whose type is unique
up to `Conv` (every non-λ subject). -/
def HasTypeDescPi.decidableCheckOfInferredUniqueAtType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context)
    {subject inferredType inferredTypeClassifier targetType : RawTerm scope}
    {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (inferred : HasTypeDescPi profile context subject inferredType)
    (inferredTypeTyped : HasTypeDescPi profile context inferredType inferredTypeClassifier)
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag))
    (uniqueAtSubject :
      ∀ {otherType : RawTerm scope},
        HasTypeDescPi profile context subject otherType → Conv inferredType otherType) :
    Decidable (HasTypeDescPi profile context subject targetType) :=
  match Conv.decidableOfWellTypedInWfContextDesc wellFormed inferredTypeTyped targetTyped with
  | isTrue converts =>
      isTrue (HasTypeDescPi.conv targetLevel targetFlag inferred converts targetTyped)
  | isFalse notConvertible =>
      isFalse (fun derivation => notConvertible (uniqueAtSubject derivation))

end FX1Poly.Typed
