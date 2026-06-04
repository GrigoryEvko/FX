import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepSubst

/-! # FX1Poly/Core/EtaPostponementOverBeta
    — η-postponement over β: per-η-constructor quasi-commutation (OSN-B3..B6)

The open βη-SN assembly (`accUnionBetaEta`, OSN-B1) consumes one hypothesis,
`EtaQuasiCommutesOverBeta = QuasiCommutesRightOverLeft Step Step.eta`: an η-step followed by a β/ι-step
can be reordered into a β/ι-step followed by a βη-star reduction.  Discharging it is a critical-pair
analysis with ONE obligation per η constructor (etaLam, etaPair, etaModIntro, etaPathLam, etaGlueIntro).
This file collects those per-constructor lemmas; OSN-B6 assembles them by casing on the η-step.

## The postponement shape (etaLam, OSN-B3)

The η-step `etaLam : Step.eta (etaLamSource f) f` is contraction of `lam[ app[ weaken f, newestVar ] ]` to
`f`.  Given a following β/ι-step `f → c`, the witness is `d := etaLamSource c`:

  * `etaLamSource f → etaLamSource c` by a SINGLE β/ι-step — the congruence lift of `f → c` through the
    etaLam context `lam ∘ app ∘ weaken` (`Step.weaken` for the weakening, `Step.cong`/`StepChildren.here`
    for the structural layers).  This is `Step.etaLamSourceCongruence`.
  * `etaLamSource c →η c` by one etaLam η-step — the βη-star tail (`UnionStar.tailRight`).

The β/ι-step is lifted UNIFORMLY (any `Step`, via the general `Step.weaken`), so no case analysis on the
kind of β/ι-step is needed.  The η-contraction duplicates nothing here, so the tail is a single η-step;
the `UnionStar` (not single-step) target is what the abstract Geser criterion requires and what the
duplicating constructors (etaPair, OSN-B4) will genuinely use.

## Zero-axiom verification

`Step.cong` + `StepChildren.here` + `Step.weaken` + `UnionStar.tailRight`/`refl` — all structural.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- Lift a β/ι-step under the etaLam source context `lam[ app[ weaken _, newestVar ] ]`: a step on the
inner function becomes a single step on the whole etaLam source, by congruence through the lambda binder,
the application head, and the weakening. -/
theorem Step.etaLamSourceCongruence {scope : Nat}
    {innerFunction reduct : RawTerm scope}
    (betaStep : Step innerFunction reduct) :
    Step (RawTerm.etaLamSource innerFunction) (RawTerm.etaLamSource reduct) :=
  Step.cong .gen_lam ()
    (StepChildren.here .childNil
      (Step.cong .gen_app ()
        (StepChildren.here
          (.childCons RawTerm.newestVar .childNil : RawTermChildren [0] (scope + 1))
          (Step.weaken betaStep))))

/-- **etaLam quasi-commutes over β (OSN-B3).**  An etaLam η-step then a β/ι-step reorders into a single
β/ι-step then a βη-star reduction: the etaLam case of `QuasiCommutesRightOverLeft Step Step.eta`.  The
common reduct is `etaLamSource reduct` — reached from `etaLamSource innerFunction` by the congruence lift
of the β/ι-step, and reaching `reduct` by one etaLam η-contraction. -/
theorem etaLamQuasiCommutesOverBeta {scope : Nat}
    {innerFunction reduct : RawTerm scope}
    (betaStep : Step innerFunction reduct) :
    ∃ commonReduct, Step (RawTerm.etaLamSource innerFunction) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaLamSource reduct,
   Step.etaLamSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaLam reduct)⟩

end FX1Poly.Core
