import LeanFX.Mode.Defn
import LeanFX.Syntax.Term
import LeanFX.Syntax.Raw

/-! # LeanFX — ground-up formalisation of FX in Lean 4.

This is the public root of the package.  Every public-facing
definition lives in `LeanFX/...` and is re-exported here in
dependency order.

## One kernel, two layers

A single kernel that **bypasses Lean 4's elaborator limitation
from both sides** — intrinsic typing where Lean accepts it, raw
syntax where it doesn't — and links the two via bridge functions.
Both layers live in `LeanFX/Syntax/`:

  * `LeanFX.Syntax` (intrinsic layer, `Term.lean`) — `Ty : Nat →
    Nat → Type`, `Ctx`, `Term : (Γ : Ctx) → Ty → Type`.  Typing is
    construction; constructor signatures *are* the typing rules.
    Most of the kernel lives here: substitution, reduction,
    parallel reduction, Conv, identity-proof scaffold.  ~7,800
    lines, 100% zero-axiom.

  * `LeanFX.Syntax.Raw` (raw layer, `Raw.lean`) — `Ty : Nat → Nat
    → Type` and `Term : Nat → Nat → Type` mutual, where `Ty.tyId`
    references raw `Term` values in *argument position*.  This
    sidesteps the mutual-index-signature limit
    (`feedback_lean_mutual_index_rule.md`).  Provides the
    Term-mentioning `Ty` constructors (identity types, future J
    eliminator, parametricity bridges) that the intrinsic layer
    architecturally cannot host.

## Why this works

Lean 4's elaborator forbids cross-mutual references in *mutual
inductive index family signatures*.  It admits cross-references in
*constructor argument types*.  The fix that crystallised after the
prototype: define raw `Ty/Term` MUTUAL with each other (so
`Ty.tyId` can reference raw `Term` in args), then build the
intrinsic kernel SEPARATELY on top with its own `Ty/Term/Ctx`.
Two layers, one kernel; the bridge between them is the future
`Term.toRaw : intrinsic.Term Γ T → Raw.Term level scope` and
companion lift.

## Trust base

  * Lean 4 kernel (~6 KLoC C++; accepted as TCB).
  * `LeanFX.Mode.Defn` — the four-mode enum.  Audited as input data.
  * `LeanFX.Syntax.Term` — intrinsic Ty + Ctx + Term GADT.
  * `LeanFX.Syntax.Raw` — raw mutual `Ty + Term` with `Ty.tyId`.

Everything else — substitution, reduction, conversion, typing,
subject reduction, the bidirectional checker, the elaborator —
operates *on* the kernel and physically cannot extend it. -/
