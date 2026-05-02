import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawPar

/-! # Bridge — typed↔raw correspondence

The architectural payoff of raw-aware Term: the bridge becomes
**definitional**.  Each typed reduction has its raw counterpart by
type-index alignment.

## Forward bridge

```lean
theorem Step.par.toRawBridge
    {t1 t2 : Term ctx ty rawSrc rawTgt}
    (parallelStep : Step.par t1 t2)
    (biWitness : Step.par.isBi parallelStep) :
    RawStep.par t1.toRaw t2.toRaw
```

Proof: induction on `biWitness`.  Each case is **one line**:

```lean
case betaApp body_witness arg_witness =>
  exact RawStep.par.betaApp body_witness arg_witness

case betaAppPi body_witness arg_witness =>
  exact RawStep.par.betaApp body_witness arg_witness

case betaAppDeep functionTerm body arg arg' fn_witness arg_witness =>
  exact RawStep.par.betaAppDeep fn_witness arg_witness

case betaAppPiDeep ... =>
  exact RawStep.par.betaAppDeep ...

case lam body_witness => exact RawStep.par.lam body_witness
case app fn_witness arg_witness => exact RawStep.par.app fn_witness arg_witness
... (all cong cases — one-line each)

case iotaBoolElimTrue thenBr_witness =>
  exact RawStep.par.iotaBoolElimTrue _ thenBr_witness
... (all ι cases — one-line each)
```

Total proof body: ~50 lines (vs lean-fx's bridge with 4 sorries +
~150 lines of attempted discharges).

## Backward extraction (where decidable)

```lean
def Bridge.backward (rawStep : RawStep.par r1 r2) (h : Term ctx ty r1) :
    Option (Σ t', Step.par h t' ∧ t'.toRaw = r2)
```

Used by Algo for decidable conversion.

## Source / target inversion

* `Step.par.lam_source_inv` — typed inversion: if Step.par t1 t2 has
  source `Term.lam body`, extract structure
* `Step.par.app_source_inv`, etc.

In lean-fx these used HEq-refutation tricks (per
`feedback_typed_inversion_breakthrough.md`).  In lean-fx-2 they're
direct because the type indices give Lean enough structure.

## Dependencies

* `Reduction/ParRed.lean` — typed Step.par + isBi
* `Reduction/RawPar.lean` — raw Step.par target

## Downstream consumers

* `Algo/DecConv.lean` — decidable conversion runs raw side, uses
  bridge to lift
* `Algo/Eval.lean` — fuel-bounded eval can run on raw with bridge
  back to typed

## Diff from lean-fx

* lean-fx had **4 unprovable sorries** for the dep β cases
  (betaAppPi, betaAppPiDeep) plus structural blockers on non-dep β
  (betaApp, betaAppDeep) — these were the W9.B1.x targets that
  ultimately motivated the lean-fx-2 rewrite
* lean-fx-2: zero sorries.  Every case is `RawStep.par.<ctor>
  witnesses` directly.
* Source/target inversion lemmas are direct (no HEq refutation
  detour)

Target: ~150 lines (vs lean-fx's ~600 lines across `ParToRawBridge.lean`,
`ParInversion.lean`, scaffolding helpers).

## Implementation plan (Phase 5)

1. State `Step.par.toRawBridge`
2. Induction on `Step.par.isBi`, one case per ctor — each case a
   one-liner via `exact RawStep.par.<ctor> witnesses`
3. Verify zero sorries, verify zero axioms
4. Add backward extraction (deferred — needed only by Algo)
5. Add source/target inversion lemmas
-/

namespace LeanFX2

end LeanFX2
