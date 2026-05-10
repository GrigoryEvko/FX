import LeanFX2.Foundation.Polygraph.PolyCell

/-! # Smoke/AuditPolyCell — K11.1 zero-axiom audit gate.

K11.1 ships `LeanFX2.Foundation.Polygraph.PolyCell` — the universal
n-cell type per Burroni 1993 §1.1.  This smoke gate exercises the
inductive's constructors at dim 0, dim 1, and dim 2 and verifies each
witness has empty axiom closure.

## Coverage

* `PolyCell.gen0` constructor at dim 0.
* `PolyCell.genSucc` constructor at dim 1 (source/target at dim 0).
* `PolyCell.genSucc` constructor at dim 2 (recursive — source/target at
  dim 1, which themselves recurse to dim 0).

`DecidableEq`, source/target projections, well-foundedness, and the
parallelism witness are intentionally deferred: their construction
requires the `casesOn`-with-index-equality motive recipe from
`feedback_lean_indexed_partial_match.md`, which arrives with K11.2
(`ParallelPair`) and K11.3 (`DecidableEq strengthening`).

Every `#print axioms` below MUST report "does not depend on any
axioms" per the project absolute zero-axiom commitment.  STRICT-22 —
polygraph well-formedness gate — depends on this coverage being clean.
-/

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

-- Dim-0 generator witness.
def polyCell11_gen0_smoke : PolyCell 0 :=
  PolyCell.gen0 0

-- Dim-1 cell witness with explicit source/target.
def polyCell11_genSucc_smoke : PolyCell 1 :=
  PolyCell.genSucc 0 (PolyCell.gen0 0) (PolyCell.gen0 1) 7

-- Dim-2 cell witness — confirms recursive cell construction works
-- through `genSucc` past dim 1.
def polyCell11_genSuccDeep_smoke : PolyCell 2 :=
  PolyCell.genSucc 1
    (PolyCell.genSucc 0 (PolyCell.gen0 0) (PolyCell.gen0 1) 7)
    (PolyCell.genSucc 0 (PolyCell.gen0 0) (PolyCell.gen0 1) 8)
    42

end LeanFX2.Smoke

#print axioms LeanFX2.Smoke.polyCell11_gen0_smoke
#print axioms LeanFX2.Smoke.polyCell11_genSucc_smoke
#print axioms LeanFX2.Smoke.polyCell11_genSuccDeep_smoke
