import LeanFX2.Confluence.ConvTrans

/-! Phase 7 Conv.trans zero-axiom audit (#1504 PHASE7-CONV-TRANS).

## What ships in this phase

* `Conv.transChains` (`Reduction/Conv.lean`) — chain-composition
  flavor of typed `Conv.trans`.  Given explicit `StepStar` chains
  `s →* t` and `t →* u`, produce `Conv s u` directly via
  `StepStar.append` packaged as `Conv.fromStepStar`.

* `Conv.trans_via_chains` (`Confluence/ConvTrans.lean`) —
  re-export of `Conv.transChains` in the Confluence namespace
  hierarchy for canonical discoverability alongside
  `Conv.transRaw` and `Conv.canonicalForm`.

Both verified zero-axiom.

## What remains blocked

The full `Conv.trans` (where each Conv brings its own midpoint,
not just an explicit chain) requires typed `Step.parStar.confluence`
which in turn requires strong subject reduction (term construction
via raw-step inversion at typed sources).  M06/M07 ship the type
EQUALITY part of subject reduction (see
`Term/SubjectReductionGeneral.lean`), but term construction needs
additional infrastructure (~100+ inversion cases).

See `Confluence/ConvTrans.lean`'s docstring for the detailed
shipping plan and the dependency chain.
-/

#print axioms LeanFX2.Conv.transChains
#print axioms LeanFX2.Conv.trans_via_chains
