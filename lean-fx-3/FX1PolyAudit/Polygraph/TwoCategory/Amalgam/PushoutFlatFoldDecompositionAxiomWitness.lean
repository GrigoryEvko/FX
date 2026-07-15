import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatFoldDecomposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatFoldDecompositionAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the block-diagonal fold decomposition of flat layouts and the per-slot extraction.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.shiftMapBy
#print axioms FX1Poly.Polygraph.Amalgam.shiftMapBy_length
#print axioms FX1Poly.Polygraph.Amalgam.natAddLeftCancelClean
#print axioms FX1Poly.Polygraph.Amalgam.shiftMapBy_injective
#print axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_appendLeft
#print axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_appendRight
#print axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_shiftMapBy
#print axioms FX1Poly.Polygraph.Amalgam.appendLengthNat
#print axioms FX1Poly.Polygraph.Amalgam.append_split_of_prefixLength
#print axioms FX1Poly.Polygraph.Amalgam.arityFold_hcomp_append
#print axioms FX1Poly.Polygraph.Amalgam.arityFold_id
#print axioms FX1Poly.Polygraph.Amalgam.SlotPayloadFoldsAligned
#print axioms FX1Poly.Polygraph.Amalgam.flatFold_peel
#print axioms FX1Poly.Polygraph.Amalgam.flatFold_slots_aligned
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatFoldDecomposition

end FX1PolyAudit
