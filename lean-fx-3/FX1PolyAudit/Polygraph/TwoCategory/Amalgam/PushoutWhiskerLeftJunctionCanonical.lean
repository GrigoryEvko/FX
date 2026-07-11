import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionCanonical

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionCanonical — zero-axiom gate for the r21 B1
LAYOUT-level frame-block splice + its slot count + boundary distributions (WP-AMALG-2 r21, B1 — arm b data-level)

Per-declaration zero-axiom gate for the layout splice, its cons equation, the head-merge length, the offset and
canonical slot counts, the domain / codomain boundary distributions, and the slot-count probe.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameIntoLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameIntoLayout_cons_cons
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mergeFrameIntoHead_cons_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameIntoLayout_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameIntoLayout_firingBlockLayout_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_spliceFrameIntoLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_spliceFrameIntoLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.spliceFrameIntoLayout_probeSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerLeftLayoutSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftFiringBlockMerge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftFiringBlockMergeAtFrame
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionCanonical
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionMuWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionMuSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerLeftJunctionCanonical

end FX1PolyAudit
