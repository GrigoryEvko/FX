import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutNormalForm — zero-axiom gate for the GAP-INDEXED pushout
normal form (WP-AMALG-2 r3, B2)

Per-declaration zero-axiom gate: the wall / gap NF coordinate, its witness-word computations, the base-case NF
soundness (the right-image completeness lift), the two concrete single-gap NF-collapse witnesses, and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the gap-indexed NF coordinate + witness computations
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutWallBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGapBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWord_walls
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWord_gaps
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWord_wallsGaps_blockDecompose

-- the base-case NF soundness (the right-image completeness lift) + concrete witnesses
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageCompletenessLift
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutAssocGapConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutLeftUnitGapConv

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutNormalFormGapIndexed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutNormalFormSpliceStaysWalled

end FX1PolyAudit
