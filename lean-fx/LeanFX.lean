import LeanFX.Mode.Defn
import LeanFX.Syntax.Term
import LeanFX.KernelMTT.Syntax

/-! # LeanFX — ground-up formalisation of FX in Lean 4.

This is the public root of the package.  Every public-facing
definition lives in `LeanFX/...` and is re-exported here in
dependency order.

## The two kernels

KernelV1 (`LeanFX.Syntax.Term`) is the **intrinsic** kernel: typing
is *construction*, `Term Γ m T` is a Lean type whose only inhabitants
are well-typed FX terms in context `Γ`, at mode `m`, of type `T`.
Constructor signatures *are* the typing rules.  Discovered limit:
Lean 4's mutual elaborator forbids cross-mutual references in index
family signatures (see `feedback_lean_mutual_index_rule.md`), which
makes Term-mentioning Ty constructors (identity types, dependent J)
unreachable.

KernelMTT (`LeanFX.KernelMTT.Syntax`) is the **extrinsic** kernel:
mutual `Ty` + raw `Term` admits Term in Ty's argument positions
(working around the elaborator restriction); type correctness lives
in a separate `HasType` predicate.  This is the Allais–McBride
well-scoped pattern, the standard MLTT formalization choice.
KernelMTT can express the full MTT spine — identity types, J,
parametricity modalities — that KernelV1 architecturally cannot.

## Migration plan

KernelV1 stays in active development through v1.x — vec, generic
inductive families, the parametric-type recipe.  KernelMTT advances
through v2.x in parallel (see `LeanFX.KernelMTT` for the slice
plan).  Once KernelMTT reaches feature parity (~v2.5), downstream
tooling migrates over and KernelV1 enters a 12-month deprecation
window per task #503.

## Trust base

  * Lean 4 kernel (~6 KLoC C++; accepted as TCB).
  * `LeanFX.Mode.Defn` — the four-mode enum.  Audited as input data.
  * `LeanFX.Syntax.Term` — KernelV1: intrinsic Term GADT.
  * `LeanFX.KernelMTT.Syntax` — KernelMTT: mutual Ty + raw Term.

Everything else — substitution, reduction, conversion, typing,
subject reduction, the bidirectional checker, the elaborator —
operates *on* the kernel and physically cannot extend it.  In
KernelV1, bugs in derived layers cause false rejections or non-
termination, never false acceptances.  In KernelMTT, the same holds
provided the explicit subject-reduction proofs (v2.0e+) discharge
the burden previously implicit in intrinsic constructors. -/
