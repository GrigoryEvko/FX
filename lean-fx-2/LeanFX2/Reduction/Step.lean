import LeanFX2.Term.Subst

/-! # Reduction/Step — single-step β/ι reduction

`Step : Term ctx ty rawSrc → Term ctx ty rawTgt → Prop`.  Source
and target raw indices are independent (not equal — that would be
reflexivity); a Step witnesses that the source term reduces to the
target in one step.

η-reduction is **deliberately omitted** at this layer (and from
`Step.par`).  It's added in opt-in `Reduction/Eta.lean` because
βι confluence shouldn't carry η weight.

## Contents

### Cong rules (one per binder + per eliminator)

* `appLeft : Step fn fn' → Step (Term.app fn arg) (Term.app fn' arg)`
* `appRight : Step arg arg' → Step (Term.app fn arg) (Term.app fn arg')`
* `lamBody : Step body body' → Step (Term.lam body) (Term.lam body')`
* `appPiLeft`, `appPiRight`, `lamPiBody` (dep variants)
* `pairLeft`, `pairRight`, `fstCong`, `sndCong`
* `boolElimScrutinee`, `boolElimThen`, `boolElimElse`
* `natSuccPred`, `natElimScrutinee`, `natElimZero`, `natElimSucc`,
  `natRecScrutinee`, `natRecZero`, `natRecSucc`
* `listConsHead`, `listConsTail`, `listElimScrutinee`, `listElimNil`,
  `listElimCons`
* `optionSomeValue`, `optionMatchScrutinee`, `optionMatchNone`,
  `optionMatchSome`
* `eitherInlValue`, `eitherInrValue`, `eitherMatchScrutinee`,
  `eitherMatchLeft`, `eitherMatchRight`
* `idJBase`, `idJWitness` (Identity types)

### β rules

```lean
| betaApp body arg :
    Step (Term.app (Term.lam body) arg)
         (Term.subst0 body arg)
```

**Note**: in lean-fx, this constructor's RHS had a cast through
`Ty.weaken_subst_singleton` because `Term.subst0` produced a
different type than `Term.app`'s expected codomain.  In lean-fx-2,
`Term.subst0 body arg` produces `Term ctx (cod.weaken.subst (Subst.singleton dom argRaw))`,
and `Ty.weaken_subst_singleton` makes that equal to `cod` — so we
still thread the cast, but it's the only one and it's uniform.

```lean
| betaAppPi body arg :
    Step (Term.appPi (Term.lamPi body) arg)
         (Term.subst0 body arg)
```

For dep, `Term.subst0 body arg` produces `Term ctx (cod.subst (Subst.singleton dom argRaw))`
which IS `Term.appPi`'s declared result type (per `Term.lean`'s
appPi ctor).  No cast needed.

```lean
| betaFstPair fv sv : Step (Term.fst (Term.pair fv sv)) fv
| betaSndPair fv sv : Step (Term.snd (Term.pair fv sv)) sv
```

### ι rules

* `iotaBoolElimTrue/False`
* `iotaNatElim{Zero,Succ}`, `iotaNatRec{Zero,Succ}`
* `iotaListElim{Nil,Cons}`
* `iotaOptionMatch{None,Some}`
* `iotaEitherMatch{Inl,Inr}`
* `iotaIdJRefl` (Identity type ι: `idJ base (refl _) → base`)

## Why no `Step.castBoth`/`castSource`/`castTarget` cast helpers in lean-fx-2

lean-fx had these helpers because Term values often carried
type-cast scaffolding (`Ty.weaken_subst_singleton ▸ ...`) that
Step needed to unwrap.  In lean-fx-2:
* β-rule's RHS uses `Term.subst0` directly without scaffolding
* Type indices align by construction
* Cast helpers are only needed for `betaApp` (where the cast through
  `Ty.weaken_subst_singleton` is intrinsic)

If cast helpers are still needed, they live in `Tools/Tactics/Cast.lean`.

## Dependencies

* `Term/Subst.lean` — for `Term.subst0` in β-rules

## Downstream consumers

* `Reduction/StepStar.lean` — RT closure
* `Reduction/Conv.lean` — Conv = ∃ middle term, both sides StepStar to it
* `Reduction/ParRed.lean` — Step.par lifts each Step
* `Reduction/Compat.lean` — Step.rename/subst_compatible

## Implementation plan (Phase 3)

Port from `lean-fx/LeanFX/Syntax/Reduction/Step.lean` (~611 lines)
with:
* Drop η constructors (move to Reduction/Eta.lean)
* Drop W9.B1.1/B1.2 `resultEq` parameter scaffolding for `betaAppPi`,
  `betaSndPair`, etc.
* Verify β-rule RHS types align without `Ty.weaken_subst_*` casts
  for non-arrow cases
* Add explicit raw indices on src/tgt where Lean elaboration needs hints

Target: ~400 lines (vs 611 in lean-fx).
-/

namespace LeanFX2

end LeanFX2
