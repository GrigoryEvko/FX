import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/SigmaProjectionCanonicalComputation
    — closed `fst` / `snd` on a canonical pair scrutinee PROJECT to the components (the projection computation core)

`PairCanonicalFormsCandidate.lean` ships Σ data canonicity: a closed member of the Σ candidate reduces to a
`pairCell` constructor (`pairClosedReducesToValue`).  This file pushes that into the PROJECTIONS: a closed `fst`
/ `snd` whose scrutinee is a canonical pair member reduces to the first / second component.  The Σ-projection
analog of `BoolElimCanonicalComputation` (the boolElim branch-selection analog), and a fundamental-free step toward
fst/snd reducibility.  `fst` / `snd` are the OTHER non-growing eliminators — their ι SELECTS a
component (vs. the growing recursors that apply a branch to a payload).

* `StepStar.fstScrutinee` / `StepStar.sndScrutinee` — the scrutinee-position chain congruences for the unary
  projections: a `StepStar` in the (sole) child lifts to the whole `fst` / `snd` cell.  Built from the generic
  one-hole-context chain lifter `StepStar.congAt` with `Step.cong … (StepChildren.here …)` at the head child.
* `pairCanonicalScrutineeProjectsToComponents` — the headline: a closed `fst` / `snd` on a canonical pair
  scrutinee reduces to the pair's first / second component.  The scrutinee reduces to `pairCell first second`
  (Σ data canonicity), the projection congruences carry that under `fst` / `snd`, and the matching ι rules
  (`Step.iotaFstPair` / `Step.iotaSndPair`) project out the components.

## Zero-axiom verification

`StepStar.congAt` (chain induction), `pairClosedReducesToValue` (Σ data canonicity via the candidate),
`Step.cong` / `StepChildren.here` (the scrutinee congruence step), and the `Step.iotaFstPair` /
`Step.iotaSndPair` ι constructors, chained by `StepStar.transLast`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The unary `fst` projection cell over its sole child (the pair scrutinee). -/
private abbrev fstCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons scrutinee .childNil)

/-- The unary `snd` projection cell over its sole child (the pair scrutinee). -/
private abbrev sndCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons scrutinee .childNil)

/-- **Scrutinee-position chain congruence for `fst`.**  A reduction chain in the scrutinee lifts to the whole
`fst` cell.  Instantiates the generic one-hole-context chain lifter `StepStar.congAt` with the `fst` wrapper and
the uniform `Step.cong … (here …)` at the sole (head) child. -/
theorem StepStar.fstScrutinee {scope : Nat} {scrutinee scrutineeReduct : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (fstCell scrutinee) (fstCell scrutineeReduct) :=
  StepStar.congAt
    (fun hole => fstCell hole)
    (fun stepInScrutinee => Step.cong .gen_fst () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **Scrutinee-position chain congruence for `snd`.**  Symmetric to `StepStar.fstScrutinee`. -/
theorem StepStar.sndScrutinee {scope : Nat} {scrutinee scrutineeReduct : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (sndCell scrutinee) (sndCell scrutineeReduct) :=
  StepStar.congAt
    (fun hole => sndCell hole)
    (fun stepInScrutinee => Step.cong .gen_snd () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **Closed `fst` / `snd` on a canonical pair scrutinee project to the components.**  The Σ-projection analog
of closed-bool elimination canonicity: a closed `fst` / `snd` whose scrutinee is a member of the Σ candidate
reduces to the first / second component of the pair the scrutinee evaluates to.  The scrutinee reduces to
`pairCell firstComponent secondComponent` (`pairClosedReducesToValue`), the projection congruences carry that
reduction under `fst` / `snd`, and the matching ι rules project out the components.  Fundamental-free — it uses only
Σ data canonicity plus the projection congruences and the ι rules, no fundamental theorem. -/
theorem pairCanonicalScrutineeProjectsToComponents {scrutinee : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isPairValue scrutinee) :
    ∃ firstComponent secondComponent : RawTerm 0,
      StepStar scrutinee (pairCell firstComponent secondComponent) ∧
        StepStar (fstCell scrutinee) firstComponent ∧
          StepStar (sndCell scrutinee) secondComponent := by
  obtain ⟨value, scrutineeReducesToValue, firstComponent, secondComponent,
      valueIsPair, _firstNormal, _secondNormal⟩ :=
    pairClosedReducesToValue scrutineeMember
  subst valueIsPair
  exact ⟨firstComponent, secondComponent, scrutineeReducesToValue,
    StepStar.transLast (StepStar.fstScrutinee scrutineeReducesToValue) Step.iotaFstPair,
    StepStar.transLast (StepStar.sndScrutinee scrutineeReducesToValue) Step.iotaSndPair⟩

end FX1Poly.Core
