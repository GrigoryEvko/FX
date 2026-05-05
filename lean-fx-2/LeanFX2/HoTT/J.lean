/-! # HoTT/J — J eliminator (full dependent motive)

The J eliminator with **full dependent motive** — the lean-fx v2.7
task that was deferred.

## Statement

```lean
def Term.idJ_dep
    {motive : Term ctx (Ty.id A a b) rawWitness → Type}
    (baseCase : motive (Term.refl a))
    (witness : Term ctx (Ty.id A a b) rawWitness) :
    motive witness
```

(Or analogous as a Term constructor.)  The non-dep `Term.idJ` from
`Term.lean` is recovered as the special case where motive is
constant.

## Why this matters

Full dependent J is required for:
* HoTT path induction in its strongest form
* Transport between fibers (`HoTT/Transport.lean`)
* Equivalences (`HoTT/Equivalence.lean`)
* HITs' eliminators (`HoTT/HIT/Eliminator.lean`)

Without dependent J, we have only "non-dependent identity types"
which suffice for setoid-style equational reasoning but not for
HoTT's full path-as-equality slogan.

## Implementation challenge

In Lean 4, defining a Term constructor whose result type depends
on a motive function over Term values requires either:
1. A "Term-aware Ty" (Term mentions in Ty's signature) — hits the
   Lean 4 mutual-index rule that lean-fx hit in v1.4
2. Universe codes (Tarski-style universe with `El` decoder)
3. HITs with the motive baked into the eliminator

lean-fx-2 chooses option 2 (universe codes) — Tarski universe with
`El : Term ctx (Ty.universe u) → Ty u scope`.  The motive is then a
function `Term → Term ctx Ty.universe u`.

## Dependencies

* `HoTT/Identity.lean`

## Downstream consumers

* `HoTT/Transport.lean` — `transport` is J with motive `λ p. P b`
* `HoTT/Equivalence.lean` — equivalence between fibers
* `HoTT/HIT/*` — HIT eliminators are dep-J specializations

## Implementation plan (Phase 6)

1. Universe codes (decision: which encoding — Russell vs Tarski?)
2. Define `idJ_dep` either as Term constructor or derived theorem
3. Verify computation: `idJ_dep (refl a) = baseCase` (the ι rule
   for dep J — generalizes the non-dep iotaIdJRefl)
4. Smoke: compute `J` on refl, verify path-induction examples

Target: ~200-400 lines depending on universe encoding choice.
-/

namespace LeanFX2

end LeanFX2
