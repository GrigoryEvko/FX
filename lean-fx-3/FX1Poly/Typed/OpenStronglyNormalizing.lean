import FX1Poly.Typed.BoundedGrownFundamental
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Core.StronglyNormalizingSubst

/-! # FX1Poly/Typed/OpenStronglyNormalizing
    — SN-for-well-typed, open form (the SN-043 wiring): every well-typed grown term is SN GIVEN a reducible
      closing environment

`HasTypeDescPi.stronglyNormalizingOfReducibleEnv`: for ANY context `context` (arbitrary scope), a grown derivation
`HasTypeDescPi context subject classifier` with a budget and a bound-reducible closing substitution for `context` has
a strongly-normalizing `subject`.  This is the open generalization of the closed capstone (BFT-14): the same
member→SN→reflect composition, but parameterized over an arbitrary closing environment instead of the vacuous empty
one.  The closed case (`ClosedStronglyNormalizing.lean`) is the instance `substitution := Fin.elim0`,
`envReducible := ReducibleEnvAtBounded.empty`.

## What this is, and the one residual for fully-unconditional #546

This theorem IS SN-043 modulo the Tait "reducible substitution" input: a bound-reducible closing environment for the
context.  Concretely, fully-unconditional `WfContext context → HasTypeDescPi context subject classifier →
IsStronglyNormalizing subject` reduces to ONE remaining lemma —

  `reducibleEnvOfWfContext : WfContext context → ∃ bound substitution,
       BoundExceedsPi env bound d ∧ ReducibleEnvAtBounded env bound context substitution`

— i.e. the identity (renaming) closing substitution is bound-reducible over a well-formed context.  That builder is
the classical reducible-substitution lemma: by induction on the context telescope, each variable is a reducible
member of its looked-up type via the candidate's `IsReducibilityCandidate.containsVariable` (the CR3 neutral leaf),
with the type's reducibility coming from the grown FT applied to its `WfContext.headIsType` derivation under the
prefix environment, all aligned to a common bound (max of `d`'s budget and the per-entry context budgets, lifted via
`monotoneInBound` / member cumulativity).  It is tracked as the open extension of BFT-14; the wiring here makes the
gap precise and small-surface.

## Zero-axiom verification

A three-step composition of shipped zero-axiom results: `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c) →
`stronglyNormalizing_of_memberAtBoundedSucc` (scope+1 bounded CR1) → `StepStar.stronglyNormalizing_of_subst` (SN
reflects through the closing substitution).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **SN-for-well-typed, open form (the SN-043 wiring).**  Any grown derivation, given a `BoundExceedsPi` budget and
a bound-reducible closing environment for its (arbitrary) context, has a strongly-normalizing subject.  The grown FT
(BFT-12c) gives the subject a bound-reducible member under the closing substitution; the scope+1 bounded CR1 turns
that into SN of the substituted subject; SN-reflection through the substitution returns SN of the bare subject.
Subsumes the closed capstone (instantiate the empty context's vacuous environment). -/
theorem HasTypeDescPi.stronglyNormalizingOfReducibleEnv {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (d : HasTypeDescPi profile context subject classifier)
    (budget : BoundExceedsPi env bound d)
    {substitution : RawTermSubst scope (targetScope + 1)}
    (envReducible : ReducibleEnvAtBounded env bound context substitution) :
    StepStar.IsStronglyNormalizing subject :=
  StepStar.stronglyNormalizing_of_subst substitution subject
    (stronglyNormalizing_of_memberAtBoundedSucc
      (HasTypeDescPi.fundamentalAtBoundedSucc env bound d budget substitution envReducible))

end FX1Poly.Typed
