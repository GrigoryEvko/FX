import FX1Poly.Core.GeneratorFinitePolygraph

/-! # FX1Poly/Core/GeneratorPolygraphMap
    — the explicit Generator → polygraph-generator map presenting each generator's boundary

`GeneratorFinitePolygraph.lean` establishes the FX kernel as a finite polygraph by bundling the
generator data into one record with FUNCTION fields.  This file makes the per-generator POLYGRAPH GENERATOR an
explicit object — `PolygraphGenerator`, carrying a former's tag (table index), child arity (input dimension),
and per-child binder shifts (the boundary) — and gives the explicit map `Generator.toPolygraphGenerator`
presenting each of the 203 generators with its boundary, faithfully.

This is the BOUNDARY-PRESENTED layer for the FX kernel polygraph: every generator is presented as a structured
polygraph generator with its boundary made explicit, and the presentation is FAITHFUL (injective) and INVERTIBLE
(the tag recovers the generator via the inverse table `fromTag`).  It is the substrate the
`RawCell → OmegacEWord` encoding lifts the dim-1 free monoid over.

* `PolygraphGenerator` — a kernel former presented with its boundary structure (tag + child arity + child
  boundary shifts), coherently (`boundaryArityCoherent`).
* `Generator.toPolygraphGenerator` — the presentation map (tag := `toNat`, childArity := `arity`,
  childBoundaryShifts := `binderShifts`, coherence := `binderShifts_length_eq_arity`).
* `Generator.toPolygraphGenerator_injective` — FAITHFUL: distinct generators present distinctly (via the `tag`
  field and `toNat_injective`).
* `Generator.toPolygraphGenerator_boundary` / `_tag` — the presented boundary / tag ARE `binderShifts` / `toNat`.
* `Generator.toPolygraphGenerator_recoversGenerator` — INVERTIBLE: the inverse table recovers the generator from
  the presented tag (`fromTag` round-trip), so the boundary presentation loses no information.

## Zero-axiom verification

The map is a record literal over the shipped `toNat` / `arity` / `binderShifts` + the shipped coherence; the
projection theorems are `rfl`; injectivity is `congrArg PolygraphGenerator.tag` into `toNat_injective`;
invertibility is the shipped `fromTag_toNat`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- A **polygraph generator**: a kernel former presented with its boundary structure — the `tag` (table index),
the `childArity` (input dimension = child count), and the per-child `childBoundaryShifts` (the boundary: which
child sits under how many binders), coherently (`childBoundaryShifts.length = childArity`). -/
structure PolygraphGenerator where
  /-- The table index of the former. -/
  tag : Nat
  /-- The child arity (input dimension = number of sub-cells). -/
  childArity : Nat
  /-- The per-child binder shifts — the boundary structure. -/
  childBoundaryShifts : List Nat
  /-- The boundary has one shift per child (arity↔boundary coherence). -/
  boundaryArityCoherent : childBoundaryShifts.length = childArity

/-- **The explicit Generator → polygraph-generator map**, presenting each of the 203 FX kernel generators as a
polygraph generator carrying its boundary (the per-child binder shifts). -/
def Generator.toPolygraphGenerator (generator : Generator) : PolygraphGenerator where
  tag := generator.toNat
  childArity := generator.arity
  childBoundaryShifts := generator.binderShifts
  boundaryArityCoherent := generator.binderShifts_length_eq_arity

/-- **Faithful presentation**: distinct generators present as distinct polygraph generators.  Via the `tag` field
(`congrArg`) and `Generator.toNat_injective` — the boundary presentation separates all 203 generators. -/
theorem Generator.toPolygraphGenerator_injective {firstGenerator secondGenerator : Generator}
    (mapsEqual : firstGenerator.toPolygraphGenerator = secondGenerator.toPolygraphGenerator) :
    firstGenerator = secondGenerator := by
  apply Generator.toNat_injective
  exact congrArg PolygraphGenerator.tag mapsEqual

/-- The presented boundary IS the generator's binder shifts (the map presents the right boundary data). -/
theorem Generator.toPolygraphGenerator_boundary (generator : Generator) :
    generator.toPolygraphGenerator.childBoundaryShifts = generator.binderShifts := rfl

/-- The presented tag IS the generator's table index. -/
theorem Generator.toPolygraphGenerator_tag (generator : Generator) :
    generator.toPolygraphGenerator.tag = generator.toNat := rfl

/-- **Invertible presentation**: the inverse table recovers the generator from the presented tag, so the
boundary presentation loses no information (the polygraph generator uniquely names its former). -/
theorem Generator.toPolygraphGenerator_recoversGenerator (generator : Generator) :
    Generator.fromTag generator.toPolygraphGenerator.tag = some generator :=
  Generator.fromTag_toNat generator

end FX1Poly.Core
