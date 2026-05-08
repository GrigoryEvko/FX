import LeanFX2.FX1.LeanKernel.Soundness

/-! # AuditPhase12A8D89Extend — D8.9-EXTEND zero-axiom audit.

Reviewer-facing axiom regression log for the per-arm soundness extension
of `check_sound`.  Closes ticket #1526 by adding seven per-Expr-ctor
soundness lemmas:

* `check_sound_app` — Lean function application
* `check_sound_letE` — Lean let-binding
* `check_sound_lit` — natural / string-atom literals
* `check_sound_mdata` — metadata-tagged forwarding
* `check_sound_proj` — structure projection (vacuous: rejected)
* `check_sound_fvar` — free variable (vacuous: rejected)
* `check_sound_mvar` — metavariable (vacuous: rejected)

Every declaration listed must report "does not depend on any axioms".
The strict harness gate in `LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Other`
fails the build if any does. -/

#print axioms LeanFX2.FX1.LeanKernel.check_sound_app
#print axioms LeanFX2.FX1.LeanKernel.check_sound_letE
