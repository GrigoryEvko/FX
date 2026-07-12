import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapRootComm

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapRootComm — zero-axiom gate (pure two-cup Godement swap: rootComm automorphism + count bundle)

Per-declaration zero-axiom gate for the pure cup × cup Godement block swap's `rootComm` heart and the full
count-field bundle: the join-cons localization (`unionFindJoin_cons_of_roots`, the one/two-cup concrete
`links` cons forms), the block-rotation union-find automorphism (`twoCupGodement_rootComm`), the cup/cap count
correspondences, the assembled `ArcStepSimCount` bundle, the `ArcRenameRel` read-off corollary, the concrete
non-vacuity witnesses, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  An INDEPENDENT
`#print axioms` cross-check lives in the sibling `…AxiomWitness` file. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindJoin_cons_of_roots
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_links_cons
#assert_no_axioms FX1Poly.Polygraph.twoCupArcLinks_cons

end FX1PolyAudit
