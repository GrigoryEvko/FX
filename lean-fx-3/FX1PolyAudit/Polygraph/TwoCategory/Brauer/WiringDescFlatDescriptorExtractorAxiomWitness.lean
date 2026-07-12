import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorExtractor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorExtractorAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r43 flat→descriptor
extractor — the reconstruction primitives, the Σ-bundled distant-tail builder with its decode roundtrip, the untwist-run
peel roundtrip, the head-cup extractor, the flat synthesis `flatRegionDispatch`, the firing / coverage probes, and the
machine-checked terminal state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.natLeOfBleExtract
#print axioms FX1Poly.Polygraph.crossingAt_of_wiring
#print axioms FX1Poly.Polygraph.recoverDistantIndex_roundtrip
#print axioms FX1Poly.Polygraph.extractDistantStep
#print axioms FX1Poly.Polygraph.extractDistantTail
#print axioms FX1Poly.Polygraph.extractDistantTail_decodes
#print axioms FX1Poly.Polygraph.untwistRun_roundtrip
#print axioms FX1Poly.Polygraph.extractCupHead
#print axioms FX1Poly.Polygraph.extractWorkingRegion
#print axioms FX1Poly.Polygraph.flatRegionDispatch
#print axioms FX1Poly.Polygraph.flatDispatch_firesOnHostiles
#print axioms FX1Poly.Polygraph.extractWorkingRegion_coverage
#print axioms FX1Poly.Polygraph.fxBrauer_hasFlatDescriptorExtractor
#print axioms FX1Poly.Polygraph.fxBrauer_flatDescriptorExtractorTerminalState

end FX1PolyAudit
