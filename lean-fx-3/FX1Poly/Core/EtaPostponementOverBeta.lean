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

/-! ## etaModIntro (OSN-B4, the single-strip case)

`etaModIntroSource m = modIntro[ modElim[ m ] ]` — a structural strip with no binder and no weakening, so
the postponement is etaLam's shape minus the weaken: lift the β/ι-step through two congruence layers, then
one etaModIntro η-contraction.  Single copy of `m`, so the βη-tail is a single η-step. -/

/-- Lift a β/ι-step under the etaModIntro source context `modIntro[ modElim[ _ ] ]`. -/
theorem Step.etaModIntroSourceCongruence {scope : Nat}
    {modalTerm reduct : RawTerm scope}
    (betaStep : Step modalTerm reduct) :
    Step (RawTerm.etaModIntroSource modalTerm) (RawTerm.etaModIntroSource reduct) :=
  Step.cong .gen_modIntro ()
    (StepChildren.here .childNil
      (Step.cong .gen_modElim ()
        (StepChildren.here .childNil betaStep)))

/-- **etaModIntro quasi-commutes over β (OSN-B4).**  The etaModIntro case of
`QuasiCommutesRightOverLeft Step Step.eta`: common reduct `etaModIntroSource reduct`, reached by the
congruence lift and reaching `reduct` by one etaModIntro η-contraction. -/
theorem etaModIntroQuasiCommutesOverBeta {scope : Nat}
    {modalTerm reduct : RawTerm scope}
    (betaStep : Step modalTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaModIntroSource modalTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaModIntroSource reduct,
   Step.etaModIntroSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaModIntro reduct)⟩

/-! ## etaPair (OSN-B4, the DUPLICATING case)

`etaPairSource p = pair[ fst p, snd p ]` holds TWO copies of `p`.  A β/ι-step `p → c` cannot be mirrored by
a single step on the source — one step reduces only one copy.  So the postponement genuinely uses the
multi-step βη-tail: β-reduce the `fst` copy (the single forward step), then β-reduce the `snd` copy, then
η-contract.  This is the case where `UnionStar`'s multi-step capacity is load-bearing (Klop-style
duplication, absorbed by quasi-commutation — strong commutation would fail here). -/

/-- etaPair reduce-fst: step the `fst p` copy inside `pair[ fst p, snd p ]` to `pair[ fst c, snd p ]`. -/
theorem Step.etaPairSourceReduceFst {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    Step (RawTerm.etaPairSource pairTerm)
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_fst () (.childCons reduct .childNil))
          (.childCons (.mkGen .gen_snd () (.childCons pairTerm .childNil)) .childNil))) :=
  Step.cong .gen_pair ()
    (StepChildren.here _
      (Step.cong .gen_fst () (StepChildren.here .childNil betaStep)))

/-- etaPair reduce-snd: step the remaining `snd p` copy to reach `etaPairSource reduct = pair[ fst c, snd c ]`. -/
theorem Step.etaPairSourceReduceSnd {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    Step
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_fst () (.childCons reduct .childNil))
          (.childCons (.mkGen .gen_snd () (.childCons pairTerm .childNil)) .childNil)))
      (RawTerm.etaPairSource reduct) :=
  Step.cong .gen_pair ()
    (StepChildren.there _
      (StepChildren.here .childNil
        (Step.cong .gen_snd () (StepChildren.here .childNil betaStep))))

/-- **etaPair quasi-commutes over β (OSN-B4).**  The etaPair case of `QuasiCommutesRightOverLeft Step
Step.eta`: common reduct `pair[ fst c, snd p ]` (one β/ι-step on the source), then the βη-tail β-reduces the
second copy and η-contracts — a multi-step `UnionStar` (`tailLeft` then `tailRight`). -/
theorem etaPairQuasiCommutesOverBeta {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaPairSource pairTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨_,
   Step.etaPairSourceReduceFst betaStep,
   UnionStar.tailRight
     (UnionStar.tailLeft (UnionStar.refl _) (Step.etaPairSourceReduceSnd betaStep))
     (Step.eta.etaPair reduct)⟩

/-! ## etaPathLam (OSN-B5, the cubical binder case)

`etaPathLamSource p = pathLam[ pathApp[ weaken p, newestVar ] ]` — etaLam's exact shape over the cubical
path generators `gen_pathLam`/`gen_pathApp`.  Single copy under one binder, so the proof is etaLam's,
verbatim modulo the generator names. -/

/-- Lift a β/ι-step under the etaPathLam source context `pathLam[ pathApp[ weaken _, newestVar ] ]`. -/
theorem Step.etaPathLamSourceCongruence {scope : Nat}
    {innerPath reduct : RawTerm scope}
    (betaStep : Step innerPath reduct) :
    Step (RawTerm.etaPathLamSource innerPath) (RawTerm.etaPathLamSource reduct) :=
  Step.cong .gen_pathLam ()
    (StepChildren.here .childNil
      (Step.cong .gen_pathApp ()
        (StepChildren.here
          (.childCons RawTerm.newestVar .childNil : RawTermChildren [0] (scope + 1))
          (Step.weaken betaStep))))

/-- **etaPathLam quasi-commutes over β (OSN-B5).**  The etaPathLam case of
`QuasiCommutesRightOverLeft Step Step.eta`: congruence lift then one etaPathLam η-contraction. -/
theorem etaPathLamQuasiCommutesOverBeta {scope : Nat}
    {innerPath reduct : RawTerm scope}
    (betaStep : Step innerPath reduct) :
    ∃ commonReduct, Step (RawTerm.etaPathLamSource innerPath) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaPathLamSource reduct,
   Step.etaPathLamSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaPathLam reduct)⟩

/-! ## etaGlueIntro (OSN-B5, the second DUPLICATING case)

`etaGlueIntroSource g = glueIntro[ glueElim g, g ]` records the glued term TWICE (once under `glueElim`,
once as the direct second child).  Like etaPair, one β/ι-step on the source reaches only the first copy, so
the βη-tail β-reduces the second and η-contracts — a multi-step `UnionStar`.  The second copy is `g`
directly (no projection wrapper), so its reduction is a single `cong`. -/

/-- etaGlueIntro reduce the `glueElim g` copy (child 0) to `glueIntro[ glueElim c, g ]`. -/
theorem Step.etaGlueIntroReduceElim {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    Step (RawTerm.etaGlueIntroSource gluedTerm)
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_glueElim () (.childCons reduct .childNil))
          (.childCons gluedTerm .childNil))) :=
  Step.cong .gen_glueIntro ()
    (StepChildren.here _
      (Step.cong .gen_glueElim () (StepChildren.here .childNil betaStep)))

/-- etaGlueIntro reduce the direct second `g` copy (child 1), reaching `etaGlueIntroSource reduct`. -/
theorem Step.etaGlueIntroReduceSecond {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    Step
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_glueElim () (.childCons reduct .childNil))
          (.childCons gluedTerm .childNil)))
      (RawTerm.etaGlueIntroSource reduct) :=
  Step.cong .gen_glueIntro ()
    (StepChildren.there _
      (StepChildren.here .childNil betaStep))

/-- **etaGlueIntro quasi-commutes over β (OSN-B5).**  The etaGlueIntro case of
`QuasiCommutesRightOverLeft Step Step.eta`: one β/ι-step on the source (the `glueElim` copy), then the
βη-tail reduces the second copy and η-contracts — a multi-step `UnionStar` (`tailLeft` then `tailRight`). -/
theorem etaGlueIntroQuasiCommutesOverBeta {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaGlueIntroSource gluedTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨_,
   Step.etaGlueIntroReduceElim betaStep,
   UnionStar.tailRight
     (UnionStar.tailLeft (UnionStar.refl _) (Step.etaGlueIntroReduceSecond betaStep))
     (Step.eta.etaGlueIntro reduct)⟩

end FX1Poly.Core
