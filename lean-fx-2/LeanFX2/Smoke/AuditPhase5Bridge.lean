import LeanFX2.Bridge

/-! Phase 5 zero-axiom audit — typed → raw parallel-reduction bridge.

The architectural payoff: lean-fx-2's raw-aware Term encoding makes
`Step.par.toRawBridge` a 54-case one-liner, every case going through
by `exact RawStep.par.<ctor> <ihs>` because raw indices align by
construction.

Compare to lean-fx, which had:
* `Term.toRaw_subst0` as a multi-page HEq cascade
* `subst0_term` vs `subst0` flavour split forcing kernel-wide
  `Subst.dropNewest` infrastructure
* 4 unprovable bridge sorries on dep β cases (betaAppPi*)
* ~600 lines across `ParToRawBridge.lean` + `ParInversion.lean` +
  scaffolding helpers

In lean-fx-2:
* Both `Term.toRaw_subst0` and `Term.toRaw_rename` are `rfl`
* No flavour split — single `Subst.singleton` with `forRaw` in the
  type index
* Zero sorries, ~85 lines total
-/

#print axioms LeanFX2.Step.par.toRawBridge
