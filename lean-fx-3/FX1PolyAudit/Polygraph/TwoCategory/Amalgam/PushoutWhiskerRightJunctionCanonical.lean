import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionCanonical

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionCanonical — zero-axiom gate for the
whiskerRight (trailing) junction merge CONV + `CanonicalFactorization` (WP-AMALG-2 r22, arm b′)

Per-declaration zero-axiom gate for the propext-safe length-append, the append boundary laws, the trailing id-block
expansion conv, the whiskerRight junction merge conv, the `CanonicalFactorization` assembly, the recon self-attack
witnesses + slot counts, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  (The propext trap: core `List.length_append` leaks propext, replaced by the cons-only `listLengthAppend`.) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.listLengthAppend
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_append
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_append
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_append_allId
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapVcompLayout_appendAllIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapVcompLayout_congrWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapVcompLayout_fusedWallToAppended
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightMergeDomEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightMergeCodEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightFiringBlockMerge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightMergeMuConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sWallTrailingBlock
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sWallTrailingBlock_allId
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightJunctionCanonicalOfExpansion
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightJunctionMuWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightJunctionMuSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sWallDoubleTrailingBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sWallDoubleTrailingBlocks_allId
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightOfWhiskerLeftWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightOfWhiskerLeftSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightOfIdWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightOfIdSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightWallHeavyWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightWallHeavySlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerRightJunctionCanonical
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_whiskerRightTrailingSplitterStaysResidual

end FX1PolyAudit
