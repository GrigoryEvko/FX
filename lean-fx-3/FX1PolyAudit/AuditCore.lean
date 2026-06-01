import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Typed.HasType
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.ReducibleTypeClosed
import FX1Poly.Core.PointwiseIffAlgebra

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

-- Pointwise-saturation of the dependent reducibility relation (the level-free FT's choice-free piIntro
-- keystone): `ReducibleTypeClosed` is closed under pointwise-iff by construction, so it carries the
-- canonical member-predicate candidate that bare `ReducibleType` cannot.  (New file outside the
-- AuditCoreSubstrate sweep's import closure, so gated per-declaration here.)
#assert_no_axioms FX1Poly.Core.ReducibleTypeClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.toClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.closedAtMemberPredicate

-- Equivalence-relation algebra of candidate pointwise-iff (the transport algebra the reducibility
-- model threads through every `ReducibleType.deterministic` candidate transfer, and the pending
-- `ReducibleType.ofPointwiseIff` congruence-closure cascade).
#assert_no_axioms FX1Poly.Core.PointwiseIff.refl
#assert_no_axioms FX1Poly.Core.PointwiseIff.symm
#assert_no_axioms FX1Poly.Core.PointwiseIff.trans
