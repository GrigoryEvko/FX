import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Core.CanonicalFormsCandidate

/-! # FX1Poly/Typed/BoundedNeutralMember
    — a variable is a bound-reducible member of any bound-reducible type (OB-1, toward OPEN SN-043)

The member-side LEAF of the neutral/identity environment (OB-3) that extends the closed BFT route
(`HasTypeDescPi.closedStronglyNormalizing`, BFT-14) to arbitrary contexts.

The closed fundamental theorem instantiated its environment at the empty context
(`ReducibleEnvAtBounded.empty` / `Fin.elim0`).  For an OPEN context the closing substitution must send each
context variable to a bound-reducible member of its (closed) type.  The simplest such member is the variable
itself: a variable is NEUTRAL and has NO reducts, so the CR3 premise (every one-step reduct is a member) holds
VACUOUSLY, and the unconditional bounded reducibility-candidate bundle
(`ReducibleTypeAtBounded.isReducibilityCandidate`) puts it in any bound-reducible type's candidate.

## Why this is unconditional

The only hypothesis is `IsReducibleTypeAtBounded env bound typeCode` (the type is bound-reducible with SOME
candidate).  Its candidate is a Girard reducibility candidate by `ReducibleTypeAtBounded.isReducibilityCandidate`
(at `scope + 1`, the UNCONDITIONAL bundle — no predicative caveat, since the gated universeCode arm supplies the
neutral-inclusion bound locally).  CR3 (`neutralExpansion`) then admits the variable with a vacuous premise:
`noStep_var` refutes every alleged reduct.  No `#672` fuel-stability, no renaming-closure — just CR3 at a
no-reduct neutral.

## Zero-axiom verification

`obtain` the candidate, re-`refine` it, then one `neutralExpansion` application whose reduct premise is closed by
`noStep_var … |>.elim`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation
open StepStar

/-- **OB-1: a variable is a bound-reducible member of any bound-reducible type.**  Given that `typeCode` is
bound-reducible-as-type (with some candidate), the variable `var index` is a bound-reducible member of it.  The
candidate is an unconditional reducibility candidate (`ReducibleTypeAtBounded.isReducibilityCandidate`), and a
variable is admitted by CR3 (`neutralExpansion`) — it is neutral (`IsNeutral.var`) and its reduct premise is
vacuous (`noStep_var`).  The member leaf the neutral/identity environment (OB-3) cons-feeds at every context
position. -/
theorem IsReducibleMemberAtBounded.ofVariable {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm (scope + 1)} (index : Fin (scope + 1))
    (typeReducible : IsReducibleTypeAtBounded env bound typeCode) :
    IsReducibleMemberAtBounded env bound typeCode (.mkGen .gen_var index .childNil) := by
  obtain ⟨candidate, candidateReducible⟩ := typeReducible
  refine ⟨candidate, candidateReducible, ?_⟩
  exact (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).neutralExpansion
    (IsNeutral.var index)
    (fun reduct stepFromVariable => (noStep_var index stepFromVariable).elim)

end FX1Poly.Typed
