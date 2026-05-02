import LeanFX2.HoTT.NTypes

/-! # HoTT/Univalence — the univalence axiom (long-term: derived)

Univalence is the principle that **type equivalence equals type
equality**:

```lean
axiom Univalence : ∀ (A B : Type), Equiv (Id Type A B) (Equiv A B)
```

(Voevodsky's formulation: the canonical map `Id Type A B → Equiv A B`
is itself an equivalence.)

## The 0-axiom commitment problem

Univalence is *not* provable in standard MLTT.  To get univalence
without `axiom`:

1. **Cubical type theory** — interpret types as filling Kan complex,
   univalence is a theorem of the Kan structure.  This requires
   adding `Path` types with face/degeneracy operations and a
   substantial new computation rule infrastructure.

2. **Models** — interpret in simplicial sets, etc.  Meta-theoretic;
   not internal to Lean.

3. **Postulate** — accept `axiom`.

## lean-fx-2's stance

**Short term**: postulate univalence with `@[univalence_postulate]`
attribute.  Downstream theorems that depend on it carry the
attribute (propagation tracked).  This is *one* documented exception
to the zero-axiom rule, scoped to this file.

**Long term**: derive univalence via a cubical layer (deferred to
v3.x — requires `Path` types as a separate level above Id, or
extending `Ty` with face operations).

## What's available without univalence

Even without univalence, lean-fx-2 has:
* Identity types (Id, refl, J)
* Path composition, inverse, groupoid laws
* Transport
* Equivalence (≃)
* n-type stratification

Univalence is needed for:
* "propositional univalence" on a Tarski universe (lean-fx task v3.24)
* Function extensionality (provable from univalence)
* Higher inductive types' eliminators with full faithfulness

## Postulate

```lean
@[univalence_postulate]
axiom Univalence (A B : Type) : Equiv (Id Type A B) (Equiv A B)
```

## Funext from univalence

```lean
theorem funext {f g : A → B} (h : ∀ x, Id (f x) (g x)) : Id f g
```

Provable from Univalence + `Pi`-type elimination.

## Dependencies

* `HoTT/NTypes.lean`

## Downstream consumers

* `HoTT/HIT/*` — HITs assume univalent universe for full coherence
* Anywhere needing function extensionality

## Implementation plan (Phase 6)

1. State Univalence as `axiom` + `@[univalence_postulate]`
2. Derive funext from Univalence
3. Smoke tests: equivalence Inv, extensionality on ID
4. Long-term task: derive Univalence from cubical layer (Phase 6+)
-/

namespace LeanFX2

end LeanFX2
