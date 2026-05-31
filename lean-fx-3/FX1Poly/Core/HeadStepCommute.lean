import FX1Poly.Core.HeadStep
import FX1Poly.Core.RawTermFresh
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/HeadStepCommute
    — weak-head reduction commutes with renaming and substitution

A weak-head-normal dispatching reducibility interpretation (and equally normalization by evaluation /
decidable conversion) interprets a type-code after weak-head reduction — both under binders, where the
code is renamed, and after type substitution, where it is substituted.  For those readings to stay
coherent, `HeadStep` (`HeadStep.lean`) must commute with both operations:

  `HeadStep term reduct → HeadStep (rename rho term) (rename rho reduct)`
  `HeadStep term reduct → HeadStep (subst sigma term) (subst sigma reduct)`

Both reduce to the β-arm: the head redex `app (lam body) argument` renames/substitutes to a head redex
of the renamed/substituted body (under one more binder) and argument — by defeq, since the `gen_app` /
`gen_lam` heads are concrete — and its contractum `subst0 body argument` is reshaped by
`RawTerm.rename_subst0_commute` / `RawTerm.subst0_subst_commute`.  The congruence arm is exactly the
induction hypothesis re-wrapped under the (concrete-`gen_app`-headed) application.

## Zero-axiom verification

Induction on the `HeadStep` derivation.  The β-arm rewrites only the contractum (the redex shape
reduces by defeq, as in `Step.subst` / `Step.rename`); the congruence arm is the induction hypothesis.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head reduction commutes with renaming.**  The head β-redex `app (lam body) argument` renames
to a head β-redex of the renamed body (under the lifted renaming) and renamed argument; its contractum
is reshaped by `RawTerm.rename_subst0_commute`.  The congruence arm is the induction hypothesis under
the renamed application. -/
theorem HeadStep.rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (headStep : HeadStep term reduct) :
    HeadStep (RawTerm.rename rawRenaming term) (RawTerm.rename rawRenaming reduct) := by
  induction headStep with
  | beta =>
      rw [RawTerm.rename_subst0_commute]
      exact HeadStep.beta
  | appCongruence _functionStep functionInductiveHypothesis =>
      exact HeadStep.appCongruence functionInductiveHypothesis

/-- **Weak-head reduction commutes with substitution.**  The head β-redex `app (lam body) argument`
substitutes to a head β-redex of the substituted body (under the lifted substitution) and substituted
argument; its contractum is reshaped by `RawTerm.subst0_subst_commute`.  The congruence arm is the
induction hypothesis under the substituted application. -/
theorem HeadStep.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (headStep : HeadStep term reduct) :
    HeadStep (RawTerm.subst substitution term) (RawTerm.subst substitution reduct) := by
  induction headStep with
  | beta =>
      rw [RawTerm.subst0_subst_commute]
      exact HeadStep.beta
  | appCongruence _functionStep functionInductiveHypothesis =>
      exact HeadStep.appCongruence functionInductiveHypothesis

end FX1Poly.Core
