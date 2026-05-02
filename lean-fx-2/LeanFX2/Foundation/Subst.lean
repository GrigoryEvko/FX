import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawSubst

/-! # Subst — joint type/raw substitution.

`Subst level source target` is the joint substitution structure:

```
structure Subst (level source target : Nat) where
  forTy  : Fin source → Ty level target
  forRaw : RawTermSubst source target
```

A single Subst handles both type-level substitution (via `forTy`) and
raw-level substitution (via `forRaw`).  Used uniformly throughout the
kernel — no separate `singleton` vs `termSingleton` flavors.

## Operations

* `Subst.identity : Subst level scope scope`
* `Subst.lift : Subst level src tgt → Subst level (src+1) (tgt+1)` — under a binder
* `Subst.compose : Subst a b → Subst b c → Subst a c`
* `Subst.singleton : (substituent : Ty level scope) (rawArg : RawTerm scope) →
                     Subst level (scope+1) scope`
* `Ty.subst : Ty level src → Subst level src tgt → Ty level tgt`
* `Ty.rename` via `Subst` adapted from a `Renaming`

## Critical unification vs lean-fx

lean-fx had TWO singletons:
* `Subst.singleton substituent` with `forRaw = RawTermSubst.dropNewest`
* `Subst.termSingleton substituent rawArg` with `forRaw = RawTermSubst.singleton rawArg`

The two coexisted because lean-fx's `Term.appPi`'s result type used the first
flavor (where `arg.toRaw` was lost), but the bridge to raw reduction needed the
second flavor (where `arg.toRaw` was preserved).  This split caused the 4 bridge
sorries.

**lean-fx-2 has ONE singleton**: `Subst.singleton substituent rawArg` with
`forRaw = RawTermSubst.singleton rawArg`.  Every call site supplies the rawArg —
naturally, since lean-fx-2's raw-aware Term means every typed argument has its
raw form pinned by the type index.

## Composition + lift laws

* `subst_subst : (T.subst σ).subst τ = T.subst (compose σ τ)`
* `lift_compose : (compose σ τ).lift = compose σ.lift τ.lift`
* `subst_id : T.subst Subst.identity = T`
* `weaken_subst_singleton : T.weaken.subst (singleton _ _) = T`
  (the load-bearing β-reduction cast)

These laws are axiom-free.  The `weaken_subst_singleton` lemma is uniform:
no separate `weaken_subst_termSingleton`-style variant.

## Dependencies

* `Foundation/Ty.lean` — `forTy` produces Ty values
* `Foundation/RawSubst.lean` — `forRaw` is `RawTermSubst`

## Downstream

* `Term/Subst.lean` — `TermSubst` extends `Subst` with typed-value-per-position data
* `Reduction/Subst.lean` — `Step.subst_compatible` uses `Term.subst`
-/

namespace LeanFX2

-- TODO: Subst structure (forTy + forRaw)
-- TODO: Subst.lift, Subst.identity, Subst.singleton (UNIFIED — single definition)
-- TODO: Subst.compose
-- TODO: Subst.equiv (pointwise equivalence)
-- TODO: Ty.subst (structural recursion on Ty, consults forTy + forRaw at id endpoints)
-- TODO: Ty.subst_id, Ty.subst_compose, Ty.weaken_subst_singleton, etc. (axiom-free)

end LeanFX2
