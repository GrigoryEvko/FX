import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Steiner.DecidableCellEq

/-! # FX1PolyAudit/Polygraph/Steiner/DecidableCellEq — zero-axiom gate (THE free-fragment decider)

Per-declaration zero-axiom gate for the loop-free/free-fragment word-problem decider: structural
`DecidableEq` of the integer-vector cell, reusing the Init `List Int` decider.  This is the key
deliverable — the higher word problem collapses to decidable vector equality with no propext leak.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.decideCoordinatesEqual
#assert_no_axioms FX1Poly.Polygraph.Steiner.decidableSteinerCellEq

end FX1PolyAudit
