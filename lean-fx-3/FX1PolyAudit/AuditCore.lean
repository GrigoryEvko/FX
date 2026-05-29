import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Typed.HasType

/-! # FX1PolyAudit/AuditCore — zero-axiom gate for the cell-calculus core

Persistent per-declaration `#assert_no_axioms` gate for the FX1Poly
cell substrate migrated out of lean-fx-2's `Foundation/PolyCell/Core`.

First slice: `CellSort` — the seven-sort vocabulary
(context / type / term / mode / effect / grade / protocol) over which
every PolyCell morphism (the dim-1 `FXStep sort` cells) ranges.  This
is the spine of the "morphisms on terms, types, contexts, grades"
design: a 1-cell is `PolyCell fxProfile sort 1 …` for any `sort`, so
the sort vocabulary is the first foundational brick.

Subsequent Core slices (RawTerm, RawCell, GeneratorCore, the certified
PolyCell, the certifier) append their gates here as they land.

Typed slice (design scaffold): `FX1Poly.Typed.HasType` pins the native
cells-classify-cells typing discipline (a `.term` subject classified by
a `.type` classifier) and severs the MLTT `Foundation.Ty` classifier
that lean-fx-2's typed layer still carries.  No typing theorems yet —
the real `HasType` lands once `RawTerm` is ported; this gate guards the
sort-discipline marker so the port cannot reintroduce the legacy `Ty`.
-/

#assert_no_axioms FX1Poly.Core.CellSort
#assert_no_axioms FX1Poly.Core.CellSort.all
#assert_no_axioms FX1Poly.Core.CellSort.toCode
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode
#assert_no_axioms FX1Poly.Core.CellSort.all_length

-- Typed layer (native design scaffold — cells classify cells, MLTT severed)
#assert_no_axioms FX1Poly.Typed.hasTypeSubjectSort
#assert_no_axioms FX1Poly.Typed.hasTypeClassifierSort
#assert_no_axioms FX1Poly.Typed.hasTypeContextBindingSort
#assert_no_axioms FX1Poly.Typed.hasType_classifies_term_by_type
