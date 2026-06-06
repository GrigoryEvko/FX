import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/StrongNormalizationBetaEtaUnion
    — instantiate the abstract Geser SN-of-union at the concrete FX βη relations

The abstract criterion `FX1Poly.Core.accUnion` (`StrongNormalizationUnion`) states: if `reduceLeft` is
strongly normalizing at a point, `reduceRight` is strongly normalizing everywhere, and `reduceRight`
quasi-commutes over `reduceLeft`, then the union is strongly normalizing.  This file specializes it to
`reduceLeft := Step` (β/ι) and `reduceRight := Step.eta` (η), the two halves of `Step.betaEta = Step ∪
Step.eta`.

## The defeq bridge

`Step.betaEtaSuccessor` (the accessibility successor for βη, `StepBetaEtaConfluence`) unfolds to
`Step.betaEta earlier later`, which unfolds to `Step earlier later ∨ Step.eta earlier later` — exactly
`UnionSuccessor Step Step.eta later earlier`.  So `betaEtaSuccessor_eq_unionSuccessor` holds by `rfl`, and
the abstract `accUnion` produces `Step.betaEtaStar.IsStronglyNormalizing` by definitional equality, with no
relation-transport glue.

## What `accUnionBetaEta` consumes and what remains

  * `Step.etaStar.isStronglyNormalizing` (every raw term — η strictly shrinks `RawTerm.size`,
    `Step.eta.size_decreases`) supplies the `reduceRight`-SN-everywhere premise UNCONDITIONALLY.
  * `StepStar.IsStronglyNormalizing subject` (β-SN at the subject) is the remaining input — for well-typed
    open terms this is `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`.
  * `EtaQuasiCommutesOverBeta` (η-postponement over β) is the sole hypothesis still owed; the per-η-constructor
    critical-pair analysis discharges it, after which the open βη-SN wire is unconditional.

## Zero-axiom verification

`betaEtaSuccessor_eq_unionSuccessor` is `rfl`; `accUnionBetaEta` is a direct application of the zero-axiom
`accUnion` with two shipped zero-axiom premises.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **The η-postponement crux for open βη-SN.**  η quasi-commutes over β at every scope: an η-step followed
by a β-step reorders into a β-step followed by a βη-star reduction (`QuasiCommutesRightOverLeft Step
Step.eta`).  Stated as a `∀`-scope bundle because the postponement is scope-uniform (each η constructor's
critical-pair resolution holds at every scope).  Discharged by the per-η-constructor postponement lemmas;
consumed by the open βη-SN assembly (`accUnionBetaEta`). -/
def EtaQuasiCommutesOverBeta : Prop :=
  ∀ {scope : Nat}, QuasiCommutesRightOverLeft (@Step scope) (@Step.eta scope)

/-- The βη accessibility successor IS the `Step ∪ Step.eta` union successor — both unfold to
`Step earlier later ∨ Step.eta earlier later`.  Holds by definitional unfolding, so the abstract Geser
criterion lands directly on `Step.betaEtaStar.IsStronglyNormalizing`. -/
theorem betaEtaSuccessor_eq_unionSuccessor {scope : Nat} :
    @Step.betaEtaSuccessor scope = UnionSuccessor (@Step scope) (@Step.eta scope) := rfl

/-- **Open βη strong normalization from β-SN, shipped η-SN, and the η-postponement crux.**  The Geser
SN-of-union (`accUnion`) specialized to the FX βη relations: with `EtaQuasiCommutesOverBeta` and β-strong
normalization of the subject, the subject is strongly normalizing under the full `Step.betaEta` relation.
The η-SN-everywhere premise is supplied unconditionally by `Step.etaStar.isStronglyNormalizing`. -/
theorem accUnionBetaEta {scope : Nat}
    (etaQuasiCommutes : EtaQuasiCommutesOverBeta)
    {subject : RawTerm scope}
    (betaStronglyNormalizing : StepStar.IsStronglyNormalizing subject) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  accUnion
    (fun term => Step.etaStar.isStronglyNormalizing term)
    etaQuasiCommutes
    betaStronglyNormalizing

end FX1Poly.Core
