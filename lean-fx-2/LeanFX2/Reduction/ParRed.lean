import LeanFX2.Reduction.StepStar

/-! # Reduction/ParRed — parallel reduction

`Step.par : Term ctx ty raw1 → Term ctx ty raw2 → Prop` — Tait-
Martin-Löf parallel reduction.  Reduces all positions simultaneously,
including the contracted redex.

## Why parallel reduction

Single-step `Step` is not "diamond" — two reductions from the same
term may reach different reducts that aren't joinable in one more
step.  Parallel reduction `Step.par` is diamond, and `Step.par`
chains transitively give the same reachability as `StepStar`.
Standard Tait-Martin-Löf path to confluence.

## Constructor list

### Reflexivity

```lean
| refl (t : Term ctx ty raw) : Step.par t t
```

### Cong rules (parallel — both sides may reduce)

```lean
| app : Step.par fn fn' → Step.par arg arg' →
        Step.par (Term.app fn arg) (Term.app fn' arg')
| lam : Step.par body body' →
        Step.par (Term.lam body) (Term.lam body')
| ... (mirror Step's cong list)
```

### β-rules (lift Step's β cases to parallel form)

```lean
| betaApp body body' arg arg' :
    Step.par body body' → Step.par arg arg' →
    Step.par (Term.app (Term.lam body) arg)
             (Term.subst0 body' arg')
```

Source raw is `RawTerm.app (RawTerm.lam bodyRaw) argRaw`, target
raw is `bodyRaw'.subst0 argRaw'` — directly aligned with
`RawStep.par.betaApp`'s shape.

```lean
| betaAppPi body body' arg arg' :
    Step.par body body' → Step.par arg arg' →
    Step.par (Term.appPi (Term.lamPi body) arg)
             (Term.subst0 body' arg')
```

### Deep β-rules (function/pair parallel-reduces to redex shape)

```lean
| betaAppDeep functionTerm body arg arg' :
    Step.par functionTerm (Term.lam body) →
    Step.par arg arg' →
    Step.par (Term.app functionTerm arg)
             (Term.subst0 body arg')
```

These are needed for `Term.cd`'s aggressive β-app firing.

### ι-rules (parallel)

Mirror Step's ι-list.  `iotaBoolElimTrue/False`, `iotaNatElim*`, etc.

### Deep ι-rules

For each ι rule with Deep variant — required for `Term.cd`'s
aggressive iota firing on developed shapes.

## isBi predicate (the βι gate)

```lean
inductive Step.par.isBi : Step.par t1 t2 → Prop
  | refl, app, lam, lamPi, appPi, pair, fst, snd,
    boolElim, ..., idJ — every cong rule
  | betaApp, betaAppPi, betaFstPair, betaSndPair,
    betaAppDeep, betaAppPiDeep, betaFstPairDeep, betaSndPairDeep,
    iotaBoolElimTrue, iotaBoolElimFalse, ... — every β/ι rule
  -- NO etaArrow, NO etaSigma — η is excluded
```

Used by `Bridge.lean`: only βι reductions have raw counterparts.
η-reduction is morally a separate process (reverse β); confluence
proof factors through `isBi`-restricted Step.par.

## Dependencies

* `Reduction/StepStar.lean`

## Downstream consumers

* `Reduction/Compat.lean` — Step.par.rename/subst_compatible
* `Confluence/CdLemma.lean` — Step.par.cd_lemma
* `Confluence/Diamond.lean` — diamond property
* `Bridge.lean` — typed→raw bridge gates on Step.par.isBi

## Diff from lean-fx

* No paired-predicate `parWithBi` workaround.  In lean-fx,
  `Step.parWithBi` was introduced as a paired (Step.par + isBi)
  predicate to sidestep tactic-mode failures on opaque `theorem`
  inversions.  In lean-fx-2, the typed Term carries enough structure
  (raw indices) that direct typed inversions work, eliminating the
  need for `parWithBi`.
* No `Subst.singleton` vs `Subst.termSingleton` distinction.  All
  β-rule RHS uses uniform `Term.subst0`.
* `betaAppPi` and `betaAppPiDeep` don't need a `resultEq` parameter
  (lean-fx W9.B1.1) — type index handles it.

## Implementation plan (Phase 3)

Port from `lean-fx/LeanFX/Syntax/Reduction/ParRed.lean` (~758 lines):
* Drop W9.B1.1/B1.2 `resultEq` scaffolding
* Drop η constructors (move to opt-in Eta.lean)
* Verify β-rule type alignment without `Ty.weaken_subst_*` casts
  for non-arrow cases
* Add `Step.par.isBi` inductive (already exists in lean-fx —
  port verbatim)

Target: ~500 lines.
-/

namespace LeanFX2

end LeanFX2
