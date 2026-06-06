import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorCore

/-! # FX1Poly/Core/GeneratorFinitePolygraph
    — the FX kernel as a FINITE POLYGRAPH over the 196-Generator table

The FX kernel's term former table `Generator` (196 nullary constructors, `GeneratorCore.lean`) is exactly the
generating 0-cell set of the kernel's polygraph presentation.  This file packages it as a FINITE polygraph: the
generators are indexed bijectively-on-range into `Fin 196`, and each carries its dimension (child count) and
boundary (binder shifts), coherently.

Reuses the SHIPPED §11.6.4 table validation (`GeneratorTagRoundTrip.lean`): `Generator.toNat` (the tag 0–195),
its explicit left inverse `Generator.fromTag`, the round-trip `fromTag_toNat`, and `toNat_injective`; plus the
SHIPPED `Generator.arity` (child count) / `Generator.binderShifts` (boundary) / `binderShifts_length_eq_arity`
(arity↔boundary coherence) from `GeneratorCore.lean`.  Adds the two missing FINITENESS facts:

* `Generator.toNat_lt` — every tag is `< 196`, so `toNat` embeds `Generator` into `Fin 196` (injective + bounded
  ⟹ `Generator` is finite of cardinality `≤ 196`).
* `Generator.fromTag_total_on_range` — the inverse table is TOTAL on `0–195` (every tag names a generator), the
  surjectivity-on-range completing the `Generator ≅ Fin 196` correspondence.

Then `FiniteKernelPolygraph` bundles (index + injectivity + bound + inverse table + round-trip + range-totality +
dimension + boundary + coherence) and `fxKernelPolygraph` instantiates it from the kernel's shipped data — the
witness that the FX kernel IS a finite polygraph over the 196-Generator table.  This is the Leg-3 anchor for the
`Generator → polygraph-generator` map (`GeneratorPolygraphMap`) and the `RawCell → OmegacEWord` encoding (`RawCellWordEncoding`).

## Zero-axiom verification

`toNat_lt` is `cases generator <;> decide` (each tag a literal `< 196`); `fromTag_total_on_range` is `decide` over
the bounded `∀ tag < 196` (raised `maxRecDepth` for the 196-wide table evaluation — plain `decide`, NOT
`native_decide`); the structure fields cite the shipped/new theorems.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The `toNat` tag of every generator is below the table size 196 — so `Generator.toNat` embeds `Generator` into
`Fin 196`.  With `toNat_injective` (shipped) this proves `Generator` is finite of cardinality at most 196. -/
theorem Generator.toNat_lt (generator : Generator) : generator.toNat < 196 := by
  cases generator <;> decide

set_option maxRecDepth 4000 in
/-- The inverse table `Generator.fromTag` is TOTAL on the tag range `0–195`: every tag names a generator.  The
surjectivity-on-range that, with the round-trip `fromTag_toNat`, completes the `Generator ≅ Fin 196`
correspondence.  Proved by `decide` over the bounded `∀ tag < 196` (evaluating the 196-entry table). -/
theorem Generator.fromTag_total_on_range :
    ∀ (tag : Nat), tag < 196 → (Generator.fromTag tag).isSome = true := by
  decide

/-- A FINITE POLYGRAPH presentation of a kernel: a finite generator type (indexed bijectively-on-range into
`Fin generatorCount` by `index`, with the total inverse table `inverseTable`), each generator carrying a
`dimension` (child count) and a `boundary` (binder shifts), coherently (`boundaryArityCoherent`). -/
structure FiniteKernelPolygraph where
  /-- The number of generators (the table size). -/
  generatorCount : Nat
  /-- The table index assigned to each generator. -/
  index : Generator → Nat
  /-- Distinct generators get distinct indices (the table is collision-free). -/
  indexInjective : ∀ {firstGenerator secondGenerator : Generator},
    index firstGenerator = index secondGenerator → firstGenerator = secondGenerator
  /-- Every index is below the table size (the generators embed into `Fin generatorCount`). -/
  indexBounded : ∀ generator : Generator, index generator < generatorCount
  /-- The inverse table, recovering a generator from its index. -/
  inverseTable : Nat → Option Generator
  /-- The inverse table is a left inverse of `index` (the index round-trips). -/
  inverseTable_index : ∀ generator : Generator, inverseTable (index generator) = some generator
  /-- The inverse table is total on the index range (every index names a generator). -/
  inverseTable_totalOnRange : ∀ tag : Nat, tag < generatorCount → (inverseTable tag).isSome = true
  /-- The dimension (child count) of each generator. -/
  dimension : Generator → Nat
  /-- The boundary (the per-child binder shifts) of each generator. -/
  boundary : Generator → List Nat
  /-- The boundary has one entry per child (arity↔boundary coherence). -/
  boundaryArityCoherent : ∀ generator : Generator, (boundary generator).length = dimension generator

/-- **The FX kernel IS a finite polygraph over the 196-Generator table.**  The 196 generators are indexed
injectively (`toNat_injective`) and boundedly (`toNat_lt`) into `Fin 196`, with the total inverse table
`fromTag` (round-trip `fromTag_toNat` + range-totality `fromTag_total_on_range`); each generator carries its
dimension (`arity` = child count) and boundary (`binderShifts`), coherently (`binderShifts_length_eq_arity`).
The Leg-3 anchor: the kernel's former table is a finite polygraph presentation, the substrate the
`Generator → polygraph-generator` map and the `RawCell → OmegacEWord` encoding build on. -/
def fxKernelPolygraph : FiniteKernelPolygraph where
  generatorCount := 196
  index := Generator.toNat
  indexInjective := Generator.toNat_injective
  indexBounded := Generator.toNat_lt
  inverseTable := Generator.fromTag
  inverseTable_index := Generator.fromTag_toNat
  inverseTable_totalOnRange := Generator.fromTag_total_on_range
  dimension := Generator.arity
  boundary := Generator.binderShifts
  boundaryArityCoherent := Generator.binderShifts_length_eq_arity

end FX1Poly.Core
