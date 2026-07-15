import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatFoldDecomposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatFoldDecomposition — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the block-diagonal fold decomposition of flat layouts and the per-slot extraction.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftMapBy
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftMapBy_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.natAddLeftCancelClean
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftMapBy_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_appendLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_appendRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monotoneMapGet_shiftMapBy
#assert_no_axioms FX1Poly.Polygraph.Amalgam.appendLengthNat
#assert_no_axioms FX1Poly.Polygraph.Amalgam.append_split_of_prefixLength
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFold_hcomp_append
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFold_id
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SlotPayloadFoldsAligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatFold_peel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatFold_slots_aligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatFoldDecomposition

end FX1PolyAudit
