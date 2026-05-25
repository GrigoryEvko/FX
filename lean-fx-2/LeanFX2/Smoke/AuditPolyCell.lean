import LeanFX2.Foundation._deprecated_polygraph.PolyCell

/-! # Smoke/AuditPolyCell — K11.1 zero-axiom audit gate.

K11.1 ships `LeanFX2.Foundation._deprecated_polygraph.PolyCell` — the globular
polygraph cell type per Burroni 1993 §1.1, with intrinsic
parallelism enforced by the dim-0 boundary indices `(sourceVtx,
targetVtx)`.  This smoke gate exercises the inductive's three
constructors at dim 0, dim 1, and dim 2 and verifies each witness
has empty axiom closure.

## Coverage

* `PolyCell.atom` constructor at dim 0 (boundary is the trivial
  self-loop `(vtx, vtx)`).
* `PolyCell.arrow` constructor at dim 1 (source / target dim-0
  atoms at possibly-distinct vertices).
* `PolyCell.cell` constructor at dim 2 (source / target are
  dim-1 arrows that SHARE globular boundary `(0, 1)`; parallelism
  is enforced by the shared boundary indices — any attempt to mix
  arrows with non-matching boundary indices would be a type
  error).

`DecidableEq`, source/target/idx projections, well-foundedness,
horizontal composition, and the explicit `ParallelPair` predicate
are intentionally deferred: their construction requires the
`casesOn`-with-index-equality motive recipe from
`feedback_lean_indexed_partial_match.md`, which arrives with K11.2
(`ParallelPair` + projections) and K11.3 (`DecidableEq`
strengthening).

Every `#print axioms` below MUST report "does not depend on any
axioms" per the project absolute zero-axiom commitment.  STRICT-22
(polygraph well-formedness gate) depends on this coverage being
clean.
-/

namespace LeanFX2.Smoke

open LeanFX2.Foundation._deprecated_polygraph

-- Dim-0 atom witness — a generator at vertex 0.
def polyCell11_atom_smoke : PolyCell 0 0 0 :=
  PolyCell.atom 0

-- Dim-1 arrow witness from atom at vertex 0 to atom at vertex 1.
def polyCell11_arrow_smoke : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7

-- Dim-2 cell witness — confirms intrinsic parallelism: source and
-- target are dim-1 arrows that SHARE globular boundary `(0, 1)`.
-- Constructing a dim-2 cell with non-matching boundaries (e.g.
-- arrows from 0→1 and 5→9) is rejected by the unifier because the
-- `PolyCell 1` instances would carry different index annotations.
def polyCell11_cell_smoke : PolyCell 2 0 1 :=
  PolyCell.cell
    (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
    (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
    42

end LeanFX2.Smoke

#print axioms LeanFX2.Smoke.polyCell11_atom_smoke
#print axioms LeanFX2.Smoke.polyCell11_arrow_smoke
#print axioms LeanFX2.Smoke.polyCell11_cell_smoke
