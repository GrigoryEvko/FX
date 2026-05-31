import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Typed.HasType
import FX1Poly.Core.GeneratorTagRoundTrip

/-! # FX1PolyAudit/AuditCore — zero-axiom gate for the cell-calculus core

Persistent per-declaration `#assert_no_axioms` gate for the FX1Poly
cell substrate.

`CellSort` — the seven-sort vocabulary
(context / type / term / mode / effect / grade / protocol) over which
every PolyCell morphism (the dim-1 `FXStep sort` cells) ranges.  This
is the spine of the "morphisms on terms, types, contexts, grades"
design: a 1-cell is `PolyCell fxProfile sort 1 …` for any `sort`, so
the sort vocabulary is the foundational brick.

Typed sort markers: `FX1Poly.Typed.hasType*Sort` pin the native
cells-classify-cells typing discipline (a `.term` subject classified by
a `.type` classifier) and guard against reintroducing an MLTT
`Foundation.Ty` classifier.  (The `HasType` inductive itself is gated in
`AuditTyped.lean`.)
-/

#assert_no_axioms FX1Poly.Core.CellSort
#assert_no_axioms FX1Poly.Core.CellSort.all
#assert_no_axioms FX1Poly.Core.CellSort.toCode
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode
#assert_no_axioms FX1Poly.Core.CellSort.all_length

-- Typed-layer sort markers (cells classify cells: .term subject, .type classifier)
#assert_no_axioms FX1Poly.Typed.hasTypeSubjectSort
#assert_no_axioms FX1Poly.Typed.hasTypeClassifierSort
#assert_no_axioms FX1Poly.Typed.hasTypeContextBindingSort
#assert_no_axioms FX1Poly.Typed.hasType_classifies_term_by_type

-- §11.6.4 Generator-table validation (#230): the FX0 prefix-code tag assignment
-- `Generator.toNat` is collision-free (injective), proved via the explicit left
-- inverse `Generator.fromTag` and its per-constructor round-trip.  The head byte
-- of the cell serialization therefore uniquely identifies the generator.
#assert_no_axioms FX1Poly.Core.Generator.fromTag
#assert_no_axioms FX1Poly.Core.Generator.fromTag_toNat
#assert_no_axioms FX1Poly.Core.Generator.toNat_injective
