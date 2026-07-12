import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapWires

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapWires — zero-axiom gate (pure two-cup Godement swap: links + wires)

Per-declaration zero-axiom gate for the pure cup × cup Godement block swap's two shipped legs: the atomic
position-freedom of a single cup's links, the two-cup LINKS byte-identity (and the `nextFresh` / `loops` /
`cupEventNodes` / `capEventNodes` companions), the OPEN-WIRE block transform, the concrete width-6 non-vacuity
witnesses, and the honesty markers / false-keystone pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  An INDEPENDENT
`#print axioms` cross-check lives in the sibling `…AxiomWitness` file. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCupArc_links_positionFree
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_nextFresh_positionFree
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_links_eq
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_nextFresh_eq
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_loops_eq
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_cupEventNodes_eq
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_capEventNodes_eq
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_openWires_blockSwap
#assert_no_axioms FX1Poly.Polygraph.twoCupSwap_concrete_links
#assert_no_axioms FX1Poly.Polygraph.twoCupSwap_concrete_openWires
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupSwapLinksBytewiseIdentical
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupSwapOpenWireBlockTransform
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupGodementSwapSim
#assert_no_axioms FX1Poly.Polygraph.arcGodementSamePartitionFreshProof_staysFalse
#assert_no_axioms FX1Poly.Polygraph.arcPeelGeneralSignature_staysFalse
#assert_no_axioms FX1Poly.Polygraph.arcGodementSwapRenameableProof2_staysFalse

end FX1PolyAudit
