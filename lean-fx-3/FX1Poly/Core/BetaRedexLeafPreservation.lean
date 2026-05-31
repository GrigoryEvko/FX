import FX1Poly.Core.HasCertifiedIntros
import FX1Poly.Core.RawTermSubst0

/-! # Foundation/PolyCell/Core/BetaRedexLeafPreservation
   — beta-redex leaf preservations

Ships the **base cases** of the structural subst0-preservation
theorem, focused on the shapes that appear as the BODY of a beta
redex.

## What this ships

For each simple body shape `b`, a preservation lemma:

  given `argCert : HasCertifiedCellDim0 rawArg` (when needed),
  prove `HasCertifiedCellDim0 (RawTerm.subst0 b rawArg)`.

These are the leaf cases of the structural induction on `body` for
SR-beta.  Each closes by `rw [subst0_X_reduces]; exact intro` — the
same compositional template as the nullary-leaf and compound
preservations.

## Coverage

Beta redex `app (lam body) arg`, decomposed by body's shape:

1. **Variable body 0** — `body = var 0`:
   * `subst0_var_zero_preservation` — requires arg's cert.
2. **Variable body (k+1)** — `body = var (k+1)`:
   * `subst0_var_succ_preservation` — returns var k cert.
3. **Closed nullary bodies** — `body = X` for nullary closed X:
   * `subst0_unit_preservation`
   * `subst0_boolTrue_preservation`
   * `subst0_boolFalse_preservation`
   * `subst0_natZero_preservation`
   * `subst0_listNil_preservation`
   * `subst0_optionNone_preservation`

The variable cases are the eta of beta: `(lam x. x) arg = arg`
and `(lam x. var k) arg = var (k-1)`.  The closed nullary cases
witness that variable-free bodies are invariant under
substitution.

## Why these matter for SR-beta

In SR-beta as a structural induction on `body`, the leaf cases
(this file) discharge the base of the induction.  The inductive
cases (compound generators) reduce to recursive calls on the
children's preservations.

Each of these lemmas is a single-step proof and demonstrates
the compositional pattern that scales to the full theorem.

## Zero-axiom verification

Each lemma closes by definitional reduction (`rfl`-shaped subst0
reduction lemmas from `RawTermSubst0.lean`) plus a single `exact`
of a `HasCertifiedCellDim0` intro from `HasCertifiedIntros.lean`.
No tactics that touch propext / Quot.sound / Classical.choice.

Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Additional subst0 reduction probes

`RawTermSubst0.lean` ships `subst0_var_zero`, `subst0_var_succ_one_smoke`
(scope-1 specific), and `subst0_unit_smoke`.  This section adds the
general var-succ form and the remaining closed-nullary reductions. -/

/-- **Probe: subst0 reduces on `var (k+1)` (general k).**

`RawTerm.subst0 (var (k+1)) rawArg = var k`.

Generalizes `RawTerm.subst0_var_succ_one_smoke` from scope = 1
to arbitrary scope.  Closes by `rfl` via the singleton
substitution's positional dispatch. -/
theorem RawTerm.subst0_var_succ_reduces
    {scope : Nat} (predIndex : Nat)
    (hBound : predIndex + 1 < scope + 1)
    (rawArg : RawTerm scope) :
    RawTerm.subst0
        (.mkGen .gen_var
          (⟨predIndex + 1, hBound⟩ : Fin (scope + 1))
          .childNil)
        rawArg =
      .mkGen .gen_var
        (⟨predIndex, Nat.lt_of_succ_lt_succ hBound⟩ : Fin scope)
        .childNil := rfl

/-- **Probe: subst0 reduces on `gen_boolTrue`.** -/
theorem RawTerm.subst0_boolTrue_reduces
    {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_boolTrue () .childNil) rawArg =
      (.mkGen .gen_boolTrue () .childNil : RawTerm scope) := rfl

/-- **Probe: subst0 reduces on `gen_boolFalse`.** -/
theorem RawTerm.subst0_boolFalse_reduces
    {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_boolFalse () .childNil) rawArg =
      (.mkGen .gen_boolFalse () .childNil : RawTerm scope) := rfl

/-- **Probe: subst0 reduces on `gen_natZero`.** -/
theorem RawTerm.subst0_natZero_reduces
    {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_natZero () .childNil) rawArg =
      (.mkGen .gen_natZero () .childNil : RawTerm scope) := rfl

/-- **Probe: subst0 reduces on `gen_listNil`.** -/
theorem RawTerm.subst0_listNil_reduces
    {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_listNil () .childNil) rawArg =
      (.mkGen .gen_listNil () .childNil : RawTerm scope) := rfl

/-- **Probe: subst0 reduces on `gen_optionNone`.** -/
theorem RawTerm.subst0_optionNone_reduces
    {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_optionNone () .childNil) rawArg =
      (.mkGen .gen_optionNone () .childNil : RawTerm scope) := rfl

/-! ## Section 2 — Beta-redex leaf preservations

Each lemma takes the form: given an argument certified at the
outer scope, the subst0 of a leaf body against that argument is
certified at the outer scope. -/

/-- **Beta-redex: `(lam (var 0)) arg → arg`.**

The identity lambda's beta-reduct is the argument itself.  Cert
flows directly from the argument's certificate. -/
theorem HasCertifiedCellDim0.subst0_varZero_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (argCert : HasCertifiedCellDim0 (profile := profile) rawArg) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
        rawArg) := by
  rw [RawTerm.subst0_var_zero]
  exact argCert

/-- **Beta-redex: `(lam (var (k+1))) arg → var k`.**

A lambda over a higher-indexed variable's beta-reduct discards the
argument (the var index k+1 didn't reference the bound variable).
Cert flows from `HasCertifiedCellDim0.var k`. -/
theorem HasCertifiedCellDim0.subst0_varSucc_preservation
    {profile : PolyProfile} {scope : Nat} (predIndex : Nat)
    (hBound : predIndex + 1 < scope + 1)
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        (.mkGen .gen_var
          (⟨predIndex + 1, hBound⟩ : Fin (scope + 1))
          .childNil)
        rawArg) := by
  rw [RawTerm.subst0_var_succ_reduces]
  exact HasCertifiedCellDim0.var
    (⟨predIndex, Nat.lt_of_succ_lt_succ hBound⟩ : Fin scope)

/-- **Beta-redex: `(lam unit) arg → unit`.**

Closed nullary body is invariant under substitution. -/
theorem HasCertifiedCellDim0.subst0_unit_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_unit () .childNil) rawArg) := by
  rw [RawTerm.subst0_unit_smoke]
  exact HasCertifiedCellDim0.unit

/-- **Beta-redex: `(lam true) arg → true`.** -/
theorem HasCertifiedCellDim0.subst0_boolTrue_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_boolTrue () .childNil) rawArg) := by
  rw [RawTerm.subst0_boolTrue_reduces]
  exact HasCertifiedCellDim0.boolTrue

/-- **Beta-redex: `(lam false) arg → false`.** -/
theorem HasCertifiedCellDim0.subst0_boolFalse_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_boolFalse () .childNil) rawArg) := by
  rw [RawTerm.subst0_boolFalse_reduces]
  exact HasCertifiedCellDim0.boolFalse

/-- **Beta-redex: `(lam zero) arg → zero`.** -/
theorem HasCertifiedCellDim0.subst0_natZero_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_natZero () .childNil) rawArg) := by
  rw [RawTerm.subst0_natZero_reduces]
  exact HasCertifiedCellDim0.natZero

/-- **Beta-redex: `(lam nil) arg → nil`.** -/
theorem HasCertifiedCellDim0.subst0_listNil_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_listNil () .childNil) rawArg) := by
  rw [RawTerm.subst0_listNil_reduces]
  exact HasCertifiedCellDim0.listNil

/-- **Beta-redex: `(lam none) arg → none`.** -/
theorem HasCertifiedCellDim0.subst0_optionNone_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 (.mkGen .gen_optionNone () .childNil) rawArg) := by
  rw [RawTerm.subst0_optionNone_reduces]
  exact HasCertifiedCellDim0.optionNone

end FX1Poly.Core
