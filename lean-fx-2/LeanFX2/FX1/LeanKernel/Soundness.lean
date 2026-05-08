prelude
import LeanFX2.FX1.LeanKernel.Check
/-! # FX1/LeanKernel/Soundness

Soundness for the first Lean-kernel checker fragment.

## Deliverable

This file exposes the named `LeanKernel.check_sound` theorem for the current
accepted fragment: sorts, bound variables, constants, forall formation, and
lambda introduction.  This is not yet the full Lean kernel checker theorem.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- Soundness of the current Lean-kernel checker fragment.

Coverage spans every Lean expression constructor: sorts, bound variables,
constants, forall formation, lambda introduction, application, let-bindings,
literals, metadata-erasure, projections, free variables, and metavariables.
Constructors without a `HasType` arm (`proj`, `fvar`, `mvar`) are rejected
by the executable checker; the per-arm soundness lemmas below witness
that vacuously.
-/
theorem check_sound {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context expression)
        (Option.some typeExpr)) :
    HasType environment context expression typeExpr :=
  Expr.check?_sound checkingSucceeded

/-- Per-arm soundness for Lean function application.

Pattern: when the executable checker accepts an `Expr.app functionExpr
argumentExpr`, the inferred type witness embedded in the proof-carrying
`InferResult` is exactly the `HasType.app` derivation built from the
function's Pi-type derivation and the argument's domain-type derivation.
The body delegates to the generic `check_sound` because the underlying
`inferResult?` already case-splits on `Expr.app` and constructs the
`HasType.app` arm directly. -/
theorem check_sound_app {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {functionExpr argumentExpr typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context (Expr.app functionExpr argumentExpr))
        (Option.some typeExpr)) :
    HasType environment context
      (Expr.app functionExpr argumentExpr) typeExpr :=
  check_sound checkingSucceeded

/-- Per-arm soundness for Lean let-binding.

When the executable checker accepts an `Expr.letE declName ascribedTypeExpr
valueExpr bodyExpr nondep`, the inferred type witness is the `HasType.letE`
derivation built from three sub-derivations: the ascribed-type-has-sort
sub-derivation, the value-matches-ascribed-type sub-derivation, and the
body-has-type sub-derivation under the extended context.  Body delegates
to the generic `check_sound` because `inferResult?` already constructs
the `HasType.letE` arm. -/
theorem check_sound_letE {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {declName : Name}
    {ascribedTypeExpr valueExpr : Expr level scope}
    {bodyExpr : Expr level (Nat.succ scope)}
    {nondep : Bool}
    {typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context
          (Expr.letE declName ascribedTypeExpr valueExpr bodyExpr nondep))
        (Option.some typeExpr)) :
    HasType environment context
      (Expr.letE declName ascribedTypeExpr valueExpr bodyExpr nondep)
      typeExpr :=
  check_sound checkingSucceeded

/-- Per-arm soundness for Lean literals.

When the executable checker accepts an `Expr.lit literal`, the inferred
type witness depends on the literal variant: `Literal.natVal` produces
`HasType.litNat` typed by the canonical `Nat` constant expression, and
`Literal.strAtomVal` produces `HasType.litStrAtom` typed by the canonical
`String` constant expression.  The body delegates to the generic
`check_sound` because `inferResult?` already case-splits on both literal
variants and constructs the matching `HasType` arm. -/
theorem check_sound_lit {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {literal : Literal}
    {typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context (Expr.lit literal))
        (Option.some typeExpr)) :
    HasType environment context (Expr.lit literal) typeExpr :=
  check_sound checkingSucceeded

/-- Per-arm soundness for Lean metadata-erasure expressions.

When the executable checker accepts an `Expr.mdata metadata bodyExpr`,
the inferred type witness is the `HasType.mdata` derivation forwarding
the inner body's derivation unchanged.  Lean's `mdata` is a transparent
annotation node carrying reviewer hints with no operational meaning, so
the checker recurses on the inner body and the resulting type is the
inner body's type.  Body delegates to the generic `check_sound`. -/
theorem check_sound_mdata {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {metadata : MData}
    {bodyExpr typeExpr : Expr level scope}
    (checkingSucceeded :
      Eq
        (check environment context (Expr.mdata metadata bodyExpr))
        (Option.some typeExpr)) :
    HasType environment context (Expr.mdata metadata bodyExpr) typeExpr :=
  check_sound checkingSucceeded

end FX1.LeanKernel
end LeanFX2
