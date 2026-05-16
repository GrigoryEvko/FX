import LeanFX2.Term.SubjectReductionPar

/-! # Smoke/AuditSubjectReductionPar — `Step.par` closed-type subject reduction

Reviewer log: confirms `Step.par.preserves_isClosedTy` and
`Step.parStar.preserves_isClosedTy` ship at zero axioms.

These are load-bearing primitives for CONVTRANS-C Phase A1 follow-up:
the universal chain lift dispatcher needs to bridge two-Ty existential
results from `lift_full_term` callbacks back to fixed-Ty results at
closed-typed children (e.g. `Term.intervalOpp innerValue` with
`innerValue : Term ctx Ty.interval _`).

The IsClosedTy-indexed Step.par SR mirrors the existing Step SR
(`Step.preserves_isClosedTy` in `Term/SubjectReductionGeneral.lean`)
at the parallel-step level.  Same proof recipe: induction on the
parallel step, `all_goals first | ...` fallbacks cover all 129 ctors.

## Root status

Zero-axiom. -/

#print axioms LeanFX2.Step.par.preserves_isClosedTy
#print axioms LeanFX2.Step.parStar.preserves_isClosedTy
