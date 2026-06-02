import FX1Poly.Core.WeakHeadStep

/-! # Foundation/PolyCell/Core/WeakHeadStepNormalForms
    — terms with no weak-head step (data constructors, Π-codes)

`WeakHeadStep` (`WeakHeadStep.lean`) fires only on `gen_app`-rooted terms (β / function-congruence) and
on the ten eliminator roots (root-ι / scrutinee-congruence).  Every other head — a data constructor or a
type former such as `piTyCode` — is weak-head NORMAL.  This file records those normal-form facts; they
are the refutations that the weak-head-step/`Step` commutation (`IotaHeadStep.commuteWithStep`,
`WeakHeadStep.commuteWithStep`) and the "weak-head-normal closed under `Step`" lemma consume — e.g. a
root-ι redex's constructor scrutinee cannot itself weak-head step, and a Π-code is never a `whnfExpand`
subject.

Each proof is uniform: `cases` the hypothetical `WeakHeadStep`; the β / scrutinee-congruence
constructors conclude `gen_app`/eliminator-rooted subjects (impossible by index unification against a
constructor / `piTyCode` head), and the `rootIota` premise is an `IotaHeadStep` on that same non-
eliminator head, refuted by an inner `cases`.

## Zero-axiom verification

`cases weakHeadStep with | rootIota iotaStep => cases iotaStep` (every other arm auto-discarded by root
mismatch).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- A Π-code has no weak-head step (it is a type former, not an application or eliminator). -/
theorem WeakHeadStep.not_from_piTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {reduct : RawTerm scope} :
    ¬ WeakHeadStep
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `boolTrue` has no weak-head step. -/
theorem WeakHeadStep.not_from_boolTrue {scope : Nat} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_boolTrue () .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `boolFalse` has no weak-head step. -/
theorem WeakHeadStep.not_from_boolFalse {scope : Nat} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_boolFalse () .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `natZero` has no weak-head step. -/
theorem WeakHeadStep.not_from_natZero {scope : Nat} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_natZero () .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `natSucc predecessor` has no weak-head step (a constructor, not an eliminator/application). -/
theorem WeakHeadStep.not_from_natSucc {scope : Nat}
    {predecessor : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `pair firstValue secondValue` has no weak-head step. -/
theorem WeakHeadStep.not_from_pair {scope : Nat}
    {firstValue secondValue : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep
        (.mkGen .gen_pair () (.childCons firstValue (.childCons secondValue .childNil))) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `listNil` has no weak-head step. -/
theorem WeakHeadStep.not_from_listNil {scope : Nat} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_listNil () .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `listCons headValue tailValue` has no weak-head step. -/
theorem WeakHeadStep.not_from_listCons {scope : Nat}
    {headValue tailValue : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep
        (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil))) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `optionNone` has no weak-head step. -/
theorem WeakHeadStep.not_from_optionNone {scope : Nat} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_optionNone () .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `optionSome value` has no weak-head step. -/
theorem WeakHeadStep.not_from_optionSome {scope : Nat}
    {value : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_optionSome () (.childCons value .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `eitherInl value` has no weak-head step. -/
theorem WeakHeadStep.not_from_eitherInl {scope : Nat}
    {value : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_eitherInl () (.childCons value .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `eitherInr value` has no weak-head step. -/
theorem WeakHeadStep.not_from_eitherInr {scope : Nat}
    {value : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_eitherInr () (.childCons value .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- `refl rawWitness` has no weak-head step. -/
theorem WeakHeadStep.not_from_refl {scope : Nat}
    {rawWitness : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_refl () (.childCons rawWitness .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- A VARIABLE has no weak-head step — the canonical NEUTRAL head.  Together with the type-former and
constructor cases this is what makes a de Bruijn variable a weak-head-normal `neutral` leaf (e.g. the
`IsFirstOrderSimplyTyped` leaf witness for a variable base type). -/
theorem WeakHeadStep.not_from_var {scope : Nat} {index : Fin scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_var index .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- A universe code `Type@e` has no weak-head step (a type former, not an application or eliminator). -/
theorem WeakHeadStep.not_from_universeCode {scope : Nat}
    {payload : Generator.gen_universeCode.payload scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_universeCode payload .childNil) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- A Σ-code has no weak-head step (a type former, the dual of `not_from_piTyCode`). -/
theorem WeakHeadStep.not_from_sigmaTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {reduct : RawTerm scope} :
    ¬ WeakHeadStep
        (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) reduct := by
  intro weakHeadStep
  cases weakHeadStep with | rootIota iotaStep => cases iotaStep

end FX1Poly.Core
