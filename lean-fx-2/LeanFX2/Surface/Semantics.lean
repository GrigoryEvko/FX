import LeanFX2.Surface.KernelBridge

/-! # Surface/Semantics — denotational semantics for `Expr scope`

## Design choice: the bridge IS the denotation

Surface audits (2026-05-07) flagged the original B-series "bridge
correctness" tasks (B02–B12, tracker #1242–#1252) as vapourware:
eleven separate "correctness" theorems were claimed pending, but
no formal denotational ⟦·⟧ existed for `Expr scope`.  The cure is
to identify the denotation function with the bridge function:

```
  Expr.denote      e := Expr.toRawTerm?      e
  RawExpr.denote raw := RawExpr.toRawTerm? raw
```

With this identification, the eleven B-series tasks collapse:

* B02–B07 (per-ctor correctness for `boundExpr` / `unitExpr` /
  `appExpr` / `lamExpr` / `ifExpr` / `blockExpr`) become
  reduction-shape lemmas — already shipped as the R-series in
  `Surface/KernelBridgeReduction.lean` (tracker #1280).
* B08–B09 (env-aware variants for `binopExpr` / `freeNameExpr`)
  become the env-aware bridge in `Surface/KernelEnv.lean`.
* B10 (env-aware = env-free with `KernelEnv.empty`) is now
  literally the equality of two `denote` functions.
* B11 (`Expr.toRaw_rfl` extends to bridge-projection
  commutativity) is now `denote ∘ Expr.toRaw = denote` by `rfl`.
* B12 (totality on gap-free fragment) is the only remaining
  non-trivial obligation — characterising the input shapes for
  which `denote` returns `some _`.

This file ships the load-bearing definition + the rfl bridge to
the existing `toRawTerm?` operational form.  Downstream B-series
follow-ups consume `Expr.denote` rather than going around it.

## What this file does NOT do

* Define operational semantics (kernel `Step` already exists in
  `Reduction/Step.lean`; `Term.toRaw` is the operational mapping).
* Prove totality (B12 / tracker #1252 — separate commit).
* Define env-aware semantics (B10 / B-umbrella #1532 — separate
  commit using `KernelEnv` infrastructure).
-/

namespace LeanFX2.Surface

/-- Denotational semantics for the `RawExpr scope` indexed
inductive: an expression's meaning is its kernel `RawTerm`
projection via the bridge.  Returns `none` for the four bridge
gap categories enumerated in `KernelBridge.lean` (free names,
binops/unops, dot projections, non-trivial literals). -/
@[reducible] def RawExpr.denote {scope : Nat} (raw : RawExpr scope) :
    Option (RawTerm scope) :=
  RawExpr.toRawTerm? raw

/-- Denotational semantics for the decorated `Expr raw` family.
By the `Expr.toRaw_rfl` invariant, this just projects to the
`RawExpr.denote` of the underlying raw expression. -/
@[reducible] def Expr.denote {scope : Nat} {raw : RawExpr scope}
    (expr : Expr raw) : Option (RawTerm scope) :=
  Expr.toRawTerm? expr

/-- The bridge function and the denotation function are the same
function, by definition.  Subsumes the operational vs denotational
distinction at this layer of the surface stack. -/
theorem RawExpr.denote_eq_toRawTerm? {scope : Nat}
    (raw : RawExpr scope) :
    RawExpr.denote raw = RawExpr.toRawTerm? raw :=
  rfl

/-- Decorated counterpart of `RawExpr.denote_eq_toRawTerm?`. -/
theorem Expr.denote_eq_toRawTerm? {scope : Nat}
    {raw : RawExpr scope} (expr : Expr raw) :
    Expr.denote expr = Expr.toRawTerm? expr :=
  rfl

/-- Decorated denotation projects through the `Expr.toRaw_rfl`
invariant: the meaning of a decorated `Expr raw` is the meaning
of its underlying `RawExpr raw`.  This is the bridge-projection
commutativity claim of B11 (tracker #1251), now `rfl`. -/
theorem Expr.denote_eq_RawExpr_denote {scope : Nat}
    {raw : RawExpr scope} (expr : Expr raw) :
    Expr.denote expr = RawExpr.denote raw :=
  rfl

end LeanFX2.Surface
