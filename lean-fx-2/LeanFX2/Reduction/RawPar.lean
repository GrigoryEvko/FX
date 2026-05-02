import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst

/-! # Reduction/RawPar — raw parallel reduction

The raw (untyped) counterpart of `Step.par` (in `ParRed.lean`).
Operates on `RawTerm` directly — no typing, no Ctx, no Ty.

Used by:
* `Bridge.lean` — typed Step.par lifts to raw Step.par via the
  bridge theorem
* Decidability of conversion (Layer 9) when running on raw side
* Confluence of raw reduction (used as a sanity bench against typed)

## Contents

* `inductive RawStep` — single-step raw reduction (cong + β + ι)
* `inductive RawStep.par` — parallel raw reduction
* `inductive RawStepStar` — RT closure
* `RawStep.par.cd_lemma` — raw side of cd_lemma
* Raw inversion lemmas (`RawStep.par.lam_inv`, `pair_inv`,
  `boolTrue_inv`, etc.) — clean Lean-elaborable inversions because
  raw constructors aren't dep-typed

## Why raw side has clean inversions

Raw `Term.par` is a `Prop`-valued inductive on `RawTerm`.  Its
constructors don't carry dep-typed targets like `Subst.singleton`-
flavored Term values, so Lean's inversion tactic produces clean
case splits.  Typed `Step.par` inversion is harder (requires
`Term.toRaw` refutation tricks documented in lean-fx's
`feedback_typed_inversion_breakthrough.md`).

In lean-fx-2, typed inversions are *also* clean (raw indices give
the kernel enough structure), but raw side stays as the simpler
specification reference.

## Dependencies

* `Foundation/RawTerm.lean`
* `Foundation/RawSubst.lean`

## Downstream consumers

* `Bridge.lean` — `Step.par.toRawBridge : Step.par t1 t2 →
  RawStep.par t1.toRaw t2.toRaw`
* `Confluence/*` — raw confluence parallels typed; sanity check

## Diff from lean-fx

Mostly identical.  Port from `lean-fx/LeanFX/Syntax/Reduction/RawPar.lean`
(~526 lines) verbatim.  Drop η rules (consistent with isolating η).

Target: ~480 lines.
-/

namespace LeanFX2

end LeanFX2
