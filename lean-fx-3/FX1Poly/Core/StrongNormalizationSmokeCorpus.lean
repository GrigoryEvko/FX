import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.StrongNormalizationSpineExpansion

/-! # Foundation/PolyCell/Core/StrongNormalizationSmokeCorpus
    — concrete strong-normalization witnesses

A small regression corpus exercising the shipped strong-normalization machinery on representative raw cells:
a variable leaf (normal-form SN), the unit leaf (normal-form SN), and an identity β-redex (head-expansion
SN).  These are the closed and open term SN entry points the typed engine's downstream SN handoffs reduce to;
keeping concrete witnesses gated guards against regressions in `isStronglyNormalizing_of_noStep` /
`betaRedex_isStronglyNormalizing_of_contractum` and the leaf no-step lemmas.

## Zero-axiom verification

Each witness is a shipped-lemma application: `isStronglyNormalizing_of_noStep` on a leaf no-step witness
(`noStep_var` / `noStep_unit`), and `betaRedex_isStronglyNormalizing_of_contractum` for the redex (whose
identity contractum is the argument itself by `subst0` on the bound variable).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Smoke: a variable cell is strongly normalizing.**  A variable is a normal form (no `Step` fires), so
strong normalization is immediate from `isStronglyNormalizing_of_noStep` and `noStep_var`. -/
theorem smoke_variable_isStronglyNormalizing {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_var index .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_var index step)

/-- **Smoke: the unit cell is strongly normalizing.**  `unit` is a normal-form leaf. -/
theorem smoke_unit_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing (.mkGen .gen_unit () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep (fun _targetTerm step => noStep_unit step)

/-- **Smoke: the identity β-redex applied to a strongly-normalizing argument is strongly normalizing.**
`(λx. x) argument` β-contracts to `argument` (the bound variable substituted by the argument), so
head-expansion (`betaRedex_isStronglyNormalizing_of_contractum`) lifts the argument's strong normalization to
the whole redex.  The lambda body is variable zero `⟨0, Nat.succ_pos scope⟩` (no `Fin` `OfNat` numeral, which
would leak `propext`). -/
theorem smoke_identityRedex_isStronglyNormalizing {scope : Nat}
    (argument : RawTerm scope) (argumentStronglyNormalizing : IsStronglyNormalizing argument) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) .childNil))
          (.childCons argument .childNil))) :=
  betaRedex_isStronglyNormalizing_of_contractum argumentStronglyNormalizing argumentStronglyNormalizing

end FX1Poly.Core
