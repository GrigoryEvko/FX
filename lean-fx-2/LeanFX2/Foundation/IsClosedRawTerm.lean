import LeanFX2.Foundation.RawPartialRename.UnweakenInversion

/-! # Foundation/IsClosedRawTerm — Prop-valued var-0-freeness witness

A `RawTerm (scope + 1)` is **closed** at the var-0 layer when it is in
the image of `RawTerm.weaken` — equivalently, when every variable
reference inside is at position `succ _` so the term can be lowered
across one outer binder via `PartialRawRenaming.dropNewest`.

## Why this matters

The Conv cong-coverage budget (`Tools/AuditAll/GatesParity.lean`) is
structurally floored at 25 because raw-payload-carrying type formers
(`Ty.id`, `Ty.oeq`, `Ty.idStrict`, `Ty.path`, `Ty.glue`, `Ty.refine`,
`Ty.session`, `Ty.effect`) cannot enter `IsClosedTy`: the raw endpoints
they carry can in principle reference the surrounding context's
variables.  Extending `IsClosedTy` with these ctors requires a
companion predicate witnessing var-0-freeness of those raw payloads —
this file is that predicate.

`IsClosedTy.lean:46-58` documents the design rationale.

## Definition shape — Option-form witness equivalent

Rather than declaring a 78-ctor inductive paralleling `RawTerm`, we
piggy-back on the existing `RawTerm.unweaken? : RawTerm (scope + 1) →
Option (RawTerm scope)` recognizer from
`Foundation/RawPartialRename/Function.lean`.  The predicate is then
the existential

  `IsClosedRawTerm raw ↔ ∃ inner, raw = inner.weaken`

with the iff to `raw.unweaken?.isSome` proved via
`RawTerm.unweaken?_imp_weaken` (UnweakenInversion.lean).

This avoids the 78-case structural induction while remaining
Prop-valued (so `IsClosedTy` extension ctors can carry an
`IsClosedRawTerm` hypothesis without making `IsClosedTy` itself
data-bearing).

## Zero-axiom

Every declaration here is a `def` / `theorem` with `#print axioms`
clean.  The infrastructure leans entirely on the partial-renaming
inversion lemma, which is itself zero-axiom.

## Downstream consumers

* `IsClosedTy` extension ctors (`id`, `oeq`, `idStrict`, `path`,
  `glue`, `refine`, `session`, `effect`) carry `IsClosedRawTerm`
  hypotheses on their raw payloads.
* Per-family `Step.par.preserves_<Ty>_carriers` SR helpers consume
  those hypotheses to discharge the type-preservation arms of the
  129-case induction.
* CONVTRANS-C dispatch arms for `unblock-A.dispatch.{idJ, oeqJ,
  idStrictRec, refineElim, glueElim, pathApp, effectPerform,
  sessionRecv, sessionSend, oeqFunext}` and the eight
  `unblock-A.leaf.*` arms become tractable once the SR helpers ship. -/

namespace LeanFX2

/-- A raw term at `scope + 1` is **closed** at var-0 iff it is in the
image of `RawTerm.weaken`.  Equivalent to "no var-0 reference anywhere
in the term", but stated as the existential `∃ inner, raw =
inner.weaken` so the witness can be extracted directly. -/
def IsClosedRawTerm {scope : Nat} (raw : RawTerm (scope + 1)) : Prop :=
  ∃ inner : RawTerm scope, raw = inner.weaken

/-- Forward direction: a successful `unweaken?` witnesses `IsClosedRawTerm`.
The Option-form recognizer `RawTerm.unweaken?` returns `some inner`
exactly when `raw = inner.weaken`, per `unweaken?_imp_weaken`. -/
theorem IsClosedRawTerm.of_unweaken_some {scope : Nat}
    {raw : RawTerm (scope + 1)} {inner : RawTerm scope}
    (success : raw.unweaken? = some inner) :
    IsClosedRawTerm raw :=
  ⟨inner, RawTerm.unweaken?_imp_weaken raw inner success⟩

/-- Convenience: extract the inner term and the witness equation
from a closed raw.  The inner is the value `unweaken?` would have
returned, but stated directly without going through `Option`. -/
theorem IsClosedRawTerm.imp_weaken {scope : Nat}
    {raw : RawTerm (scope + 1)} (closed : IsClosedRawTerm raw) :
    ∃ inner : RawTerm scope, raw = inner.weaken :=
  closed

/-- Symmetric: from a syntactic weaken-equation, produce the
`IsClosedRawTerm` witness directly. -/
theorem IsClosedRawTerm.of_weaken_eq {scope : Nat}
    {raw : RawTerm (scope + 1)} {inner : RawTerm scope}
    (weakenEq : raw = inner.weaken) :
    IsClosedRawTerm raw :=
  ⟨inner, weakenEq⟩

/-- The weakened form of any raw term is trivially closed at the
incremented scope — `inner.weaken = inner.weaken` is the witness. -/
theorem IsClosedRawTerm.weaken_self {scope : Nat} (inner : RawTerm scope) :
    IsClosedRawTerm (inner.weaken : RawTerm (scope + 1)) :=
  ⟨inner, rfl⟩

end LeanFX2
