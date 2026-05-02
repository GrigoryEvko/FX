import LeanFX2.Term

/-! # HoTT/Identity — identity types

The Term constructor `refl rawWitness` introduces identity types.
This file establishes intro/elim/computation rules at the
metatheoretic level.

## Intro: refl is the only canonical inhabitant

```lean
theorem Term.refl_canonical : ∀ (t : Term ctx (Ty.id A r r) rawTerm),
    ∃ rawWitness, t = Term.refl rawWitness ∧ rawTerm = RawTerm.refl rawWitness
```

Used to derive equational consequences from typed identity proofs.

## Elim: J is the eliminator

`Term.idJ baseCase witness` is the J eliminator.  See `HoTT/J.lean`
for full development.  This file just establishes the basic
intro/elim correspondence.

## ι rule: J on refl reduces to base

`iotaIdJRefl` is in `Reduction/Step.lean`:
```lean
| iotaIdJRefl baseCase :
    Step (Term.idJ baseCase (Term.refl _)) baseCase
```

Confluence + canonicity gives that this is the only β/ι rule for
identity types.

## Pre-univalence assertions

This file establishes identity types without committing to univalence.
* `Id.refl`, `Id.trans`, `Id.sym` — groupoid laws (Layer 5 `Path/`)
* `transport` — Layer 5 `Transport.lean`
* `Equiv` — Layer 5 `Equivalence.lean`

Univalence is a *separate* commitment (Layer 5 `Univalence.lean`)
that turns this groupoid into a univalent universe.

## Dependencies

* `Term.lean` — `Term.refl`, `Term.idJ`

## Downstream consumers

* `HoTT/J.lean` — full dependent J
* `HoTT/Path/*` — groupoid structure
* `HoTT/Transport.lean`
* `HoTT/Equivalence.lean`
-/

namespace LeanFX2

end LeanFX2
