import FX1Poly.Core.HasCertifiedComposition
import FX1Poly.Core.BetaRedexCompoundPreservation
import FX1Poly.Core.BetaRedexEndToEnd

/-! # Foundation/PolyCell/Core/BetaRedexDoublingSpike
   — end-to-end SR-beta for the doubling-combinator body

End-to-end SR-beta theorem on a **compound** body, demonstrating
the COMPOSITION TEMPLATE that the full structural-induction mutual
block instantiates.

## What this ships

One theorem:

* `HasCertifiedCellDim0.beta_app_self_e2e` — given a cert for
  the beta redex `(λ x. app (var 0) (var 0)) argument`, produce a
  cert for the reduct `app argument argument`.  This is the simplest
  beta redex whose body is COMPOUND (not a leaf) and uses the
  SAME variable position TWICE — so the proof has to (a)
  extract `argumentCell` once from the source spine and (b) apply
  it TWICE on the target.

## Why this matters

Beta with a compound body needs the structural-induction mutual
block to handle arbitrary compound bodies (a substantial cascade,
four mutual lemmas).

This theorem covers ONE compound body shape (the doubling
combinator) directly, proving that for THIS specific body the
composition pattern works end-to-end at zero axioms.  Concretely it
demonstrates:

  1. **Source destructure**: how to extract `argCell` at sort
     `.term` from a cert on an outer `gen_app`.
  2. **Reduction by definitional equality**: how
     `RawTerm.subst0 (app (var 0) (var 0)) argument = app argument argument`
     by `rfl` because both `RawTerm.subst0` and the singleton
     substitution are `@[reducible]`.
  3. **Target rebuild**: how to apply `HasCertifiedCellDim0.app`
     with the SAME `argumentCell` for BOTH positions.

The mutual block generalizes step (2) to "any compound body in
scope+1 substituted by any argument in scope produces a cert for
the structurally-substituted body"; step (1) and step (3) are
identical.

## Architectural role: composition template

Every compound body shape's beta-redex E2E follows this template:

```
1. cases sourceCert ⟶ obtain outerCell at some sort
2. cases outerCell with | gen _ _ outerSpine
3. cases outerSpine repeatedly ⟶ extract per-child cells at .term
4. apply structural-induction subst0 to body's children using the
   extracted argumentCell
5. apply the compound HCC intro at the body's shape to rebuild
```

This instantiates the template at depth 1 (single binder, body
uses var 0 twice).  Depth-N templates follow by nesting the
destructure and using the mutual block's body-side recursive call.

## Choice of doubling combinator

The doubling combinator `(λ x. x x) argument` was chosen because:

  * **Compound body**: `app (var 0) (var 0)` is not a leaf, so
    the proof exercises the compound HCC intro path (not just
    `subst0_varZero_preservation`).
  * **Same variable twice**: tests that one extracted `argumentCell`
    can be reused at both positions — directly relevant when
    the mutual block instantiates the structural induction.
  * **No external reasoning**: every step is a definitional
    reduction or a one-line cell construction.  Zero `simp`,
    zero `omega`, zero propext-touching tactics.

Other compound shapes (`pair (var 0) (var 0)`, `listCons (var 0)
(var 0)`, etc.) follow the IDENTICAL template — just swap
`gen_app` for `gen_pair` / `gen_listCons` / etc.

## Zero-axiom verification

The proof closes via the SR-arm cases recipe + a single
`HasCertifiedCellDim0.app` invocation.  No `simp`, no
`omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **E2E SR-beta for the doubling combinator.**

The beta redex `(λ x. app (var 0) (var 0)) argument` reduces to
`app argument argument`.  Given a cert for the source, produce a cert
for the reduct.

Demonstrates the **composition template** for compound-bodied
beta reductions:

  1. Destructure source via spine cases to extract `argCell` at
     sort `.term` (the dim-0 invariant on `gen_app`'s child
     specs gives `.term` sort by construction).
  2. The reduction
     `subst0 (app (var 0) (var 0)) argument = app argument argument`
     is definitionally equal (every step is `@[reducible]`
     or `rfl` via the existing `subst0_app_reduces` +
     `subst0_var_zero` lemmas).
  3. Apply `HasCertifiedCellDim0.app argumentCell argumentCell` to rebuild
     the target — the SAME `argumentCell` for BOTH positions
     because both `var 0` occurrences substitute to the SAME
     argument.

This concrete instance is a specialization (body =
`app (var 0) (var 0)`) of the structural-induction
`HasCertifiedCellDim0.preservedBySubst0`, verifying the
COMPOSITION TEMPLATE at zero axioms. -/
theorem HasCertifiedCellDim0.beta_app_self_e2e
    {profile : PolyProfile} {scope : Nat}
    (argumentTerm : RawTerm scope)
    (domainAnn : RawTerm scope)
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons domainAnn
                      (.childCons
                        (.mkGen .gen_app ()
                          (.childCons
                            (.mkGen .gen_var
                              (⟨0, Nat.zero_lt_succ scope⟩
                                : Fin (scope + 1))
                              .childNil)
                            (.childCons
                              (.mkGen .gen_var
                                (⟨0, Nat.zero_lt_succ scope⟩
                                  : Fin (scope + 1))
                                .childNil)
                              .childNil)))
                        .childNil)))
                  (.childCons argumentTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_var
              (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
              .childNil)
            (.childCons
              (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil)
              .childNil))) : RawTerm (scope + 1))
        argumentTerm) := by
  -- Drill into the source's outer spine to extract `argumentCell`
  -- at sort `.term` (fixed by the `gen_app`-childSpec invariant).
  cases sourceCert with
  | intro _sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons _lamCell restAfterLam =>
        cases restAfterLam with
        | cons argumentCell _restNil =>
          -- `argumentCell : PolyCell profile .term 0 scope ... (.termBase argumentTerm)`.
          -- Goal:
          --   HCC (subst0 (app (var 0) (var 0)) argumentTerm)
          -- ≡def HCC (app argumentTerm argumentTerm)
          -- via subst0_app_reduces + subst0_var_zero × 2.
          -- Both reductions hold by `rfl` (subst0 and singleton are reducible).
          exact HasCertifiedCellDim0.app argumentCell argumentCell

end FX1Poly.Core
