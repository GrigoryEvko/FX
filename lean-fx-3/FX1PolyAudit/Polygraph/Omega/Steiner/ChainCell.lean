import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.ChainCell

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/ChainCell — zero-axiom gate (OMEGA-2.5 r1, B1)

Per-declaration `#assert_no_axioms` on the boundary-faithful full-chain carrier: `SteinerChainCell`, its
structural `DecidableEq`, the rowwise pole-table arithmetic kit (`addPolePair` / `addPoleTable` + the
abelian laws over the LOCAL `intAddComm` kit), the degenerate zero table, and the codimension-0
composite `composeAtFull`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The carrier + structural decidable equality
#assert_no_axioms FX1Poly.Polygraph.Steiner.SteinerChainCell
#assert_no_axioms FX1Poly.Polygraph.Steiner.decidableSteinerChainCellEq

-- The rowwise pole-table arithmetic kit
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPolePair
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPolePair_comm
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPolePair_assoc
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable_nil_left
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable_nil_right
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable_comm
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable_assoc
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPoleTable_length_eq

-- The degenerate zero pole table + zero law
#assert_no_axioms FX1Poly.Polygraph.Steiner.zeroPoleRow
#assert_no_axioms FX1Poly.Polygraph.Steiner.zeroPoleTable
#assert_no_axioms FX1Poly.Polygraph.Steiner.zeroPoleTable_length
#assert_no_axioms FX1Poly.Polygraph.Steiner.addPolePair_zeroPoleRow_left

-- The codimension-0 (top) composite
#assert_no_axioms FX1Poly.Polygraph.Steiner.gluePoleHead
#assert_no_axioms FX1Poly.Polygraph.Steiner.composeAtFull

end FX1PolyAudit
