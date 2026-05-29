import FX1Poly.Core.HasCertifiedProjections
import FX1Poly.Core.BetaRedexLeafPreservation

/-! # Foundation/PolyCell/Core/BetaRedexEndToEnd
   — end-to-end SR-beta for fixture-shaped bodies

V2-L3.1 phase D step 21 (2026-05-27).  First concrete end-to-end
SR-beta theorem.  Composes the EXTRACTION (step 20 projections)
with the REBUILD (step 18 leaf preservations) into a complete
chain: source cert → post-beta cert.

## What this ships

Two theorems:

1. **`beta_redex_projection`** — chained projection helper.
   Given `HasCertifiedCellDim0 (app (lam body) arg)`, extracts
   both children's certs: `body` at scope+1 and `arg` at scope.
   Wraps the two-step projection chain (app → lam → body) plus
   (app → arg) in one call.

2. **`beta_var_zero_e2e`** — the simplest meaningful SR-beta.
   Source: `(λ x. x) arg` (the identity lambda applied to arg).
   Target: `arg` (the substitution result).  This is the ONLY
   leaf-body case where the source cert contributes — the
   argument's certification flows through to the result via
   the var-zero preservation.

## Why closed nullary bodies are NOT shipped here

For body shapes that are closed nullary (unit/boolTrue/etc.),
the post-beta term is closed and trivially certified
INDEPENDENTLY of the source cert hypothesis.  Those theorems
would be vacuous (proved without using the cert), so they're
captured by `subst0_X_preservation` (step 18) and don't need
a separate end-to-end theorem.

For compound body shapes, the structural induction is required —
the inner subst recursively certifies the substituted children,
which depends on each child's cert (from the body cert via
deeper projections), and that recursion is the PENDING work.

## Forward-compat: scaling to compound bodies

When the structural induction lands, end-to-end SR-beta for
compound body shapes will compose:
  * `app_argument_projection` → arg cert
  * `app_function_projection` → lam cert
  * `lam_body_projection` → body cert
  * structural induction(body cert, arg cert) → subst0 body arg cert

## Zero-axiom verification

Both theorems compose existing zero-axiom lemmas.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **Beta-redex source projection (chained).**

Given a cert for the beta redex source `app (lam body) arg`,
extract both children's certs in one call.  Combines the two
projection steps:
  1. `app_function_projection` → `HCC (lam body)`
  2. `lam_body_projection` → `HCC body` at scope+1
  3. `app_argument_projection` → `HCC arg` at scope

Returns the pair (bodyCert, argCert).

Use case: the structural induction's start of body for the
SR-beta proof — extracts the inputs to the recursive call. -/
theorem HasCertifiedCellDim0.beta_redex_projection
    {profile : PolyProfile} {scope : Nat}
    (body : RawTerm (scope + 1))
    (arg : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons body .childNil))
                  (.childCons arg .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) body ∧
    HasCertifiedCellDim0 (profile := profile) arg := by
  refine ⟨?_, ?_⟩
  · -- extract body cert via lam projection of function
    have lamCert :=
      HasCertifiedCellDim0.app_function_projection
        (.mkGen .gen_lam () (.childCons body .childNil))
        arg
        cert
    exact lamCert.lam_body_projection body
  · -- extract arg cert directly
    exact HasCertifiedCellDim0.app_argument_projection
      (.mkGen .gen_lam () (.childCons body .childNil))
      arg
      cert

/-- **End-to-end SR-beta for the identity lambda.**

The simplest beta redex `(λ x. x) arg → arg`.  The argument's
certification flows through to the result via the var-zero
preservation:

  1. Source cert: `HCC (app (lam (var 0)) arg)`
  2. Extract `argCert` via `app_argument_projection`.
  3. Apply `subst0_varZero_preservation argCert` → result cert.

This is the FIRST atomic end-to-end SR-beta theorem,
demonstrating the projection + preservation chain composes
correctly at zero axioms.

Forward-compat: when the structural induction lands, this
theorem becomes a corollary of the general
`HasCertifiedCellDim0.preservedBySubst0` (specialized to
body = var 0).  Until then, this concrete instance is shipped
directly to verify the chain assembly. -/
theorem HasCertifiedCellDim0.beta_var_zero_e2e
    {profile : PolyProfile} {scope : Nat}
    (arg : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons
                      (.mkGen .gen_var
                        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                        .childNil)
                      .childNil))
                  (.childCons arg .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        (.mkGen .gen_var
          (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
          .childNil)
        arg) := by
  have argCert :=
    HasCertifiedCellDim0.app_argument_projection
      (.mkGen .gen_lam ()
        (.childCons
          (.mkGen .gen_var
            (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
            .childNil)
          .childNil))
      arg
      cert
  exact HasCertifiedCellDim0.subst0_varZero_preservation arg argCert

/-- **The SR-beta assembly bridge: full chain parametrized by
abstract subst0 preservation.**

Given:
  1. `sourceCert : HCC (app (lam body) arg)` — the beta redex source
  2. `substPreservation : HCC body → HCC arg → HCC (subst0 body arg)`
     — the body's subst preservation, ABSTRACTED as a hypothesis

Conclude: `HCC (subst0 body arg)` — the post-beta certification.

This factors SR-beta into two halves:
  * EXTRACTION — `beta_redex_projection` yields `(bodyCert, argCert)`.
  * REBUILD — `substPreservation bodyCert argCert` produces the target.

The `substPreservation` hypothesis is precisely what the future
structural induction `HasCertifiedCellDim0.preservedBySubst0`
will provide.  Plugging that theorem in HERE closes SR-beta
END-TO-END for arbitrary body shapes.

Until the structural induction lands, this theorem is the
**conceptual bridge**: callers that handle specific body shapes
(e.g., the 8 leaf preservations + 9 compound preservations
shipped in steps 18-19) can instantiate `substPreservation`
case-by-case. -/
theorem HasCertifiedCellDim0.beta_redex_assembly
    {profile : PolyProfile} {scope : Nat}
    (body : RawTerm (scope + 1))
    (arg : RawTerm scope)
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons body .childNil))
                  (.childCons arg .childNil))) : RawTerm scope))
    (substPreservation :
      HasCertifiedCellDim0 (profile := profile) body →
      HasCertifiedCellDim0 (profile := profile) arg →
      HasCertifiedCellDim0 (profile := profile) (RawTerm.subst0 body arg)) :
    HasCertifiedCellDim0 (profile := profile) (RawTerm.subst0 body arg) := by
  obtain ⟨bodyCert, argCert⟩ :=
    HasCertifiedCellDim0.beta_redex_projection body arg sourceCert
  exact substPreservation bodyCert argCert

end FX1Poly.Core
