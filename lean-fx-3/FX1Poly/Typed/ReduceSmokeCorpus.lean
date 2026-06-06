import FX1Poly.Core.ReduceOnce
import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.FireRootRedex
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeHonesty

/-! # FX1Poly/Typed/ReduceSmokeCorpus
    — the WN-grind reducer COMPUTES: concrete reduction fixtures, `rfl`-checked.

The WN-grind line proved `RawTerm.reduceOnce` sound (`reduceOnce_sound`) and complete
(`reduceOnce_eq_none_iff_isStepNormalForm`), and `RawTerm.fireRootRedex` sound + complete.  Those theorems
certify the reducer is correct WHENEVER it returns a value — but they never pin a single concrete reduct.
This file closes that gap with a closed-term smoke corpus: each fixture states the EXACT output of the
reducer on a concrete term and discharges it by `rfl` (pure kernel computation — no `decide`, no
`native_decide`, no axioms), demonstrating the entire reduction engine is non-vacuous and computes the
intended β-reducts.

Fixtures (all closed, `RawTerm 0`, built from the readable `lamCell` / `appCell` / `variableCell` /
`unitCell` constructors):

* `identityLambda` = `λ. v0`; `identityAppliedToUnit` = `(λ. v0) unit`; `constantUnitLambda` = `λ. unit`
  (body ignores the binder); `nestedIdentityApplication` = `(λ. v0) ((λ. v0) unit)`.

What the corpus demonstrates:

* **β fires, computing the right reduct** — `reduceOnce ((λ. v0) unit) = some unit`
  (`reduceOnce_betaIdentity_fires`) and, for a binder-ignoring body, `reduceOnce ((λ. unit) (λ. v0)) =
  some unit` (`reduceOnce_betaConstant_fires`: `subst0` genuinely drops the argument, not a passthrough).
* **the reducer halts on normal forms** — `reduceOnce (λ. v0) = none` and `reduceOnce unit = none`
  (`reduceOnce_identityLambda_halts` / `reduceOnce_unit_halts`).
* **a full normalization trace** — `(λ. v0) ((λ. v0) unit)` reduces in two leftmost-outermost steps to the
  normal form `unit`: `reduceOnce_nestedRedex_fires` (step 1) then `reduceOnce_betaIdentity_fires` (step 2)
  then `reduceOnce_unit_halts` (halt).  This is exactly the iteration `RawTerm.normalize` performs.
* **the normal-form detector agrees with the reducer** — `isStepNormalFormBool` reports `false` on the redex
  and `true` on the normal lambda (`isStepNormalFormBool_betaRedex_false` /
  `isStepNormalFormBool_identityLambda_true`).
* **the root-redex engine fires directly** — `fireRootRedex .gen_app () [λ.v0, unit] = some unit`
  (`fireRootRedex_betaIdentity_fires`), confirming the `gen_app`/`gen_lam` β shape and its `Unit` payload.

## Zero-axiom verification

Every theorem is `by rfl` — definitional computation of `reduceOnce` / `fireRootRedex` /
`isStepNormalFormBool` on a fully concrete term.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- `λ. v0` — the identity lambda (a normal form). -/
def identityLambda : RawTerm 0 := lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩)

/-- `(λ. v0) unit` — the identity applied to unit (a β-redex). -/
def identityAppliedToUnit : RawTerm 0 := appCell identityLambda unitCell

/-- `λ. unit` — the constant function whose body ignores the binder. -/
def constantUnitLambda : RawTerm 0 := lamCell unitCell

/-- `(λ. unit) (λ. v0)` — the constant function applied to the identity (a β-redex whose argument is
discarded by `subst0`). -/
def constantAppliedToIdentity : RawTerm 0 := appCell constantUnitLambda identityLambda

/-- `(λ. v0) ((λ. v0) unit)` — an identity application whose argument is itself a redex; reduces in two
leftmost-outermost steps to `unit`. -/
def nestedIdentityApplication : RawTerm 0 := appCell identityLambda identityAppliedToUnit

/-- **β fires with the correct reduct.**  `(λ. v0) unit` reduces to `unit` (`subst0 unit v0 = unit`). -/
theorem reduceOnce_betaIdentity_fires :
    RawTerm.reduceOnce identityAppliedToUnit = some unitCell := by rfl

/-- **β with a binder-ignoring body.**  `(λ. unit) (λ. v0)` reduces to `unit`: `subst0` discards the
argument and returns the body, confirming substitution is not a naive passthrough. -/
theorem reduceOnce_betaConstant_fires :
    RawTerm.reduceOnce constantAppliedToIdentity = some unitCell := by rfl

/-- **The reducer halts on a normal form.**  The identity lambda has no redex. -/
theorem reduceOnce_identityLambda_halts :
    RawTerm.reduceOnce identityLambda = none := by rfl

/-- **The reducer halts on a normal atom.**  `unit` is irreducible. -/
theorem reduceOnce_unit_halts :
    RawTerm.reduceOnce (unitCell : RawTerm 0) = none := by rfl

/-- **First step of a two-step normalization trace.**  Leftmost-outermost reduction fires the root redex
first, leaving `(λ. v0) unit`; the second step (`reduceOnce_betaIdentity_fires`) then reaches the normal
form `unit`. -/
theorem reduceOnce_nestedRedex_fires :
    RawTerm.reduceOnce nestedIdentityApplication = some identityAppliedToUnit := by rfl

/-- **The detector reports the redex as non-normal.** -/
theorem isStepNormalFormBool_betaRedex_false :
    RawTerm.isStepNormalFormBool identityAppliedToUnit = false := by rfl

/-- **The detector reports the identity lambda as normal.** -/
theorem isStepNormalFormBool_identityLambda_true :
    RawTerm.isStepNormalFormBool identityLambda = true := by rfl

/-- **The root-redex engine fires directly.**  `fireRootRedex` on the `gen_app` of `[λ. v0, unit]` returns
`unit` — confirming the β shape and the `Unit` payload of `gen_app`. -/
theorem fireRootRedex_betaIdentity_fires :
    RawTerm.fireRootRedex .gen_app () (.childCons identityLambda (.childCons unitCell .childNil))
      = some unitCell := by rfl

end FX1Poly.Typed
