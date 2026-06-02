import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.StrongNormalizationLeaves

/-! # Foundation/PolyCell/Core/StrongNormalizationBetaEtaLeaves
    — the SN entry points (variable / unit leaves) are robust under the eta extension (SN-045)

The decidable-conversion endgame runs over the full conversion relation `Step.betaEta = Step ∪ Step.eta`
(beta + iota + eta), not just `Step` (beta + iota).  SN-044 / SN-081 established strong normalization of
the leaves and formers over `Step`; this file opens SN-045 by lifting the SN ENTRY POINTS — the variable
and unit leaves the typed engine's SN handoffs bottom out at — to `Step.betaEtaStar.IsStronglyNormalizing`
(`Acc Step.betaEtaSuccessor`).

A leaf is beta-eta NORMAL: no `Step` fires (`noStep_var` / `noStep_unit`) and no `Step.eta` fires either
(`noEtaStep_var` / `noEtaStep_unit` — the five eta constructors `etaLam` / `etaPair` / `etaPathLam` /
`etaModIntro` / `etaGlueIntro` each demand a specific former-shaped source, none of which is a variable or
unit, so inversion closes by generator mismatch with no axioms).  A beta-eta-normal term is beta-eta-SN by
the `Acc.intro` base case `isStronglyNormalizingBetaEta_of_noBetaEtaStep`, the beta-eta analogue of
`isStronglyNormalizing_of_noStep`.

Scope note: the FORMERS over normal children (e.g. `lam unit`, `pair unit unit`) are likewise beta-eta
normal, but proving their no-`Step` leg needs the `cong` + `StepChildren` child-step inversion (the shipped
`Step.from_<former>` derived inversions feeding `noStep_unit`); that is the documented SN-045 follow-up.  The
eta-inversion leg already generalizes cleanly (former eta-inversion is the same axiom-free `cases`).

## Zero-axiom verification

`cases` on `Step.eta` at a leaf (pure generator-mismatch `noConfusion`), `Or.elim` over the
`Step.betaEta` disjunction, and `Acc.intro`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Gated per declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Eta does not fire on a variable leaf.**  Every `Step.eta` constructor requires a former-shaped source
(`lam` / `pair` / `pathLam` / `modIntro` / `glueIntro`); a variable matches none, so inversion closes by
generator mismatch. -/
theorem noEtaStep_var {scope : Nat} (index : Fin scope) {targetTerm : RawTerm scope}
    (step : Step.eta (.mkGen .gen_var index .childNil) targetTerm) : False := by
  cases step

/-- **Eta does not fire on the unit leaf.**  Same generator-mismatch inversion as `noEtaStep_var`. -/
theorem noEtaStep_unit {scope : Nat} {targetTerm : RawTerm scope}
    (step : Step.eta (.mkGen .gen_unit () .childNil) targetTerm) : False := by
  cases step

/-- **No beta-eta step implies beta-eta strong normalization.**  The `Acc.intro` base case: a term with no
`Step.betaEta` successor is `Acc Step.betaEtaSuccessor` vacuously.  The beta-eta analogue of
`isStronglyNormalizing_of_noStep`, reusable for any beta-eta-normal witness. -/
theorem isStronglyNormalizingBetaEta_of_noBetaEtaStep {scope : Nat} {term : RawTerm scope}
    (noBetaEtaStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta term reduct) :
    Step.betaEtaStar.IsStronglyNormalizing term :=
  Acc.intro term (fun reduct stepEdge => absurd stepEdge (noBetaEtaStep reduct))

/-- **The variable leaf is beta-eta strongly normalizing.**  A variable is beta-eta normal: no `Step`
(`noStep_var`) and no `Step.eta` (`noEtaStep_var`) along either side of the `Step.betaEta` disjunction. -/
theorem var_isStronglyNormalizingBetaEta {scope : Nat} (index : Fin scope) :
    Step.betaEtaStar.IsStronglyNormalizing (.mkGen .gen_var index .childNil : RawTerm scope) :=
  isStronglyNormalizingBetaEta_of_noBetaEtaStep (fun _reduct stepEdge =>
    stepEdge.elim (fun betaStep => noStep_var index betaStep)
      (fun etaStep => noEtaStep_var index etaStep))

/-- **The unit leaf is beta-eta strongly normalizing.**  Unit is beta-eta normal: no `Step`
(`noStep_unit`) and no `Step.eta` (`noEtaStep_unit`). -/
theorem unit_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing (.mkGen .gen_unit () .childNil : RawTerm scope) :=
  isStronglyNormalizingBetaEta_of_noBetaEtaStep (fun _reduct stepEdge =>
    stepEdge.elim (fun betaStep => noStep_unit betaStep)
      (fun etaStep => noEtaStep_unit etaStep))

end FX1Poly.Core
