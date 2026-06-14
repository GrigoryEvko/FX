/-! # Foundation/PolyCell/Core/ConsistencyStrength — Gödel's-ceiling tag

Addresses polycell.md §11.7.1 "Gödel's ceiling → ConsistencyStrength
as computable data".  Ships the 6-ctor inductive + total rank +
decidable LE ordering that the ProfileExtension monotonicity check
and the FX0-PolyCell `.fx0c` certificate header consume.

## What this file ships

* **`ConsistencyStrength`** — 6-ctor inductive following the spec
  table at polycell.md:5652-5659.  Five fixed ordinal-approximation
  ctors (`finitistic`, `predicative`, `impredicative`,
  `inaccessible`, `mahlo`) plus one parameterised `custom (tag : Nat)`
  for user-declared strengths above mahlo.

* **`@[reducible] toRank`** — total function to `Nat` for decidable
  comparison.  Maps the five named tiers to 0..4; `custom n` maps
  to `5 + n` (custom strengths are above all five named tiers by
  convention).

* **`@[reducible] le`** — `Prop`-valued ordering defined as
  `left.toRank ≤ right.toRank`.

* **`LE` instance** and **`Decidable LE`** instance — the latter via
  `Nat.decLe` on the ranks, so every concrete comparison reduces
  by `decide`.

Seven witness theorems pin behavior across the strength tower:

* `finitistic_le_predicative`
* `predicative_le_impredicative`
* `impredicative_le_inaccessible`
* `inaccessible_le_mahlo`
* `mahlo_le_custom_zero`
* `custom_zero_le_custom_one`
* `not_predicative_le_finitistic` — antisymmetry witness on the
  non-trivial pair.

## Why `custom (tag : Nat)` instead of `custom (tag : Name)`

The polycell.md spec uses `custom (tag : Name)` where `Name` is
`Lean.Name` (hierarchical identifier in the Lean elaborator).  The
kernel cannot import `Lean.*` without dragging the whole elaborator
into the audit tree, so this implementation substitutes `Nat` as the
user-tag carrier, keeping the substrate elaborator-independent.

The `Nat` tag is operationally sufficient for the monotonicity
check: a Lean-level proof obligation can map any `Name` to a fresh
Nat via the elaborator at admission time.  The strength tower's
ordering only requires DECIDABLE comparison; Nat suffices.

## Why `@[reducible]` on `toRank` and `le`

The `@[reducible]` attribute lets the witness theorems close by
`decide`: the rank computations + Nat.decLe reduce definitionally
at typecheck time.  Without it, `decide` falls back to runtime
evaluation that requires extra elaboration work.

## Integration with ProfileExtension

This file is the OBSERVATIONAL layer (the strength inductive +
ordering).  The integration with `ProfileExtension` carries the
strength tuple and a monotonicity field:

```lean
structure ProfileExtension ... where
  strengthBefore : ConsistencyStrength
  strengthAfter : ConsistencyStrength
  strengthMonotone : strengthBefore ≤ strengthAfter
  ...
```

The monotonicity proof obligation:
* For conservative extensions (definitional additions):
  `strengthAfter = strengthBefore`, trivially monotone.
* For axiomatic extensions (bare declarations): `strengthAfter`
  carries the named strength claim; the proof obligation is
  discharged by `decide` against this file's `LE` instance.

## Why the strength tower is monotone, not a join-semilattice

The spec uses LOWER bounds: a tag is a CLAIM about the profile's
strength, and the ordering is "strengthAfter ≥ strengthBefore".  No
finite join (max) operation is needed because:
* Sequential ProfileExtensions chain via `≤` directly.
* Combining two independent extensions (a join) isn't a primitive
  operation in the ProfileExtension calculus.

## FX0-PolyCell external-verifier discipline

Per polycell.md §11.7.1:

> the `.fx0c` certificate header carries the `ConsistencyStrength`
> tag.  The external verifier checks that the tag is MONOTONE
> through the certificate chain (extensions never decrease
> strength) but does NOT verify the tag is correct (that's a
> Layer 2 Lean proof).

This file's `ConsistencyStrength` and `LE` decision procedure are
the SOURCE OF TRUTH for both verifiers:
* The Lean-side checker uses the LE instance to discharge the
  strength monotonicity inside ProfileExtension proofs.
* The external `.fx0c` verifier serializes the tag as a single Nat
  (via `toRank`) and checks monotonicity by comparing successive
  Nats.

The Nat encoding of `toRank` is the cross-verifier ABI: any future
verifier (C / Rust / etc.) reads the same Nat tag and applies the
same numeric comparison.

## What's NOT shipped here

* `ProfileExtension` field for strength + monotonicity.
* The Gödel-climbing mechanism that adds `Con(S_n)` as a Generator
  entry with `strengthAfter = strength(S_n) + 1`.
* The strength-witness proof obligation for axiomatic extensions
  (requires per-axiom strength analysis).

## Zero-axiom verification

All 10 declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Ordinal approximation of a profile's consistency strength.

Not a formal ordinal — a computable tag tracking relative strength
for the admission contract's use.  The tag is a LOWER BOUND on
what the profile can prove about weaker systems.

Six tiers from polycell.md §11.7.1:

* `finitistic`     — PRA / bounded arithmetic
* `predicative`    — PA / predicative analysis
* `impredicative`  — Zermelo / power set
* `inaccessible`   — ZFC + inaccessible cardinal
* `mahlo`          — ZFC + Mahlo cardinal
* `custom n`       — user-declared, ordinally above `mahlo` (the
                     `Nat` parameter `n` distinguishes user-
                     declared strengths).

The `custom` ctor uses `Nat` instead of `Lean.Name` (per the
spec's `tag : Name` slot) so the substrate stays
elaborator-independent.  Operationally sufficient for the
monotonicity check — see the file docstring. -/
inductive ConsistencyStrength where
  | finitistic
  | predicative
  | impredicative
  | inaccessible
  | mahlo
  | custom (tag : Nat)
  deriving DecidableEq, Repr

namespace ConsistencyStrength

/-- Numeric rank for decidable comparison.  The five named tiers
map to 0..4; `custom n` maps to `5 + n` so every custom strength
is above all five named strengths. -/
@[reducible] def toRank : ConsistencyStrength → Nat
  | .finitistic     => 0
  | .predicative    => 1
  | .impredicative  => 2
  | .inaccessible   => 3
  | .mahlo          => 4
  | .custom n       => 5 + n

/-- Ordering on consistency strengths: `left ≤ right` iff
`left.toRank ≤ right.toRank` (Nat ordering). -/
@[reducible] def le (left right : ConsistencyStrength) : Prop :=
  left.toRank ≤ right.toRank

end ConsistencyStrength

instance : LE ConsistencyStrength := ⟨ConsistencyStrength.le⟩

/-- Decidable `≤` on consistency strengths via `Nat.decLe` on the
ranks.  Lets every concrete comparison close by `decide`. -/
instance (left right : ConsistencyStrength) : Decidable (left ≤ right) :=
  Nat.decLe left.toRank right.toRank

/-! ## Witness theorems (7 pins across the strength tower)

These theorems witness the chain of monotonic comparisons across
the strength tower.  Each closes by `decide` -- the `Decidable LE`
instance defined above reduces every concrete comparison to a
`Nat.decLe` evaluation. -/

theorem finitistic_le_predicative :
    ConsistencyStrength.finitistic ≤ ConsistencyStrength.predicative := by decide

theorem predicative_le_impredicative :
    ConsistencyStrength.predicative ≤ ConsistencyStrength.impredicative := by decide

theorem impredicative_le_inaccessible :
    ConsistencyStrength.impredicative ≤ ConsistencyStrength.inaccessible := by decide

theorem inaccessible_le_mahlo :
    ConsistencyStrength.inaccessible ≤ ConsistencyStrength.mahlo := by decide

theorem mahlo_le_custom_zero :
    ConsistencyStrength.mahlo ≤ ConsistencyStrength.custom 0 := by decide

theorem custom_zero_le_custom_one :
    ConsistencyStrength.custom 0 ≤ ConsistencyStrength.custom 1 := by decide

/-- Antisymmetry witness: `predicative` is strictly above
`finitistic`, so the reverse comparison fails. -/
theorem not_predicative_le_finitistic :
    ¬ (ConsistencyStrength.predicative ≤ ConsistencyStrength.finitistic) := by decide

end FX1Poly.Core
