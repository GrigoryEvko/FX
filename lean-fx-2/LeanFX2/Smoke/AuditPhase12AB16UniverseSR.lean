import LeanFX2.Term.SubjectReductionUniverse

/-! # Smoke/AuditPhase12AB16UniverseSR — SR at Ty.universe types audit.

Audits the universe-type subject-reduction theorems shipped in
`Term/SubjectReductionUniverse.lean`.

## Audited declarations

* `Step.preserves_ty_universe` — single Step at universe types.
* `StepStar.preserves_ty_universe` — chain extension.

Both are one-line corollaries of the generic
`Step.preserves_isClosedTy` / `StepStar.preserves_isClosedTy`
at the `IsClosedTy.universe` closed-witness.

## Scope adjustment per directive

The original CUMUL-6.2 / CUMUL-6.3 framing referenced
`Step.cumulUpInner`, which is NOT shipped yet (CUMUL-3.1 pending).
Adapted scope: SR at universe types via existing β/ι rules.  The
smoke audit demonstrates that:

* No existing Step rule fires INSIDE a `Term.cumulUp` payload.
  Therefore reductions on cumulUp-wrapped terms are restricted to
  the outer-shape — and there ARE no Step rules that reduce a
  whole `Term.cumulUp` to a different Term shape (no β/ι rule on
  `cumulUp`).  Universe type preservation holds vacuously for
  that shape: there are no reductions to track.
* For Terms typed at `Ty.universe lvl ...` whose Step is one of
  the existing rules (e.g., a Step.appLeft inside a cumulUp's
  outer raw — non-existent because cumulUp is opaque to Step at
  the outer level), the universe type preservation follows from
  the closed-leaf nature of `Ty.universe`.

The vacuous-but-real preservation is the honest milestone.  Future
addition of Step.cumulUpInner (CUMUL-3.1) will require extending
this audit with a non-vacuous case for inner reductions.
-/

namespace LeanFX2

#print axioms Step.preserves_ty_universe
#print axioms StepStar.preserves_ty_universe

end LeanFX2
