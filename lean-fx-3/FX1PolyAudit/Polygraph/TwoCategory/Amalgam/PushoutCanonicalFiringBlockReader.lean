import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFiringBlockReader

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFiringBlockReader — zero-axiom gate for the r17
canonical firing-block slot-count spec + the `id`-case canonical upgrade (WP-AMALG-2 r17, B4)

Per-declaration zero-axiom gate for the SPEC backbone (`wallTagCount`, `finestGapWidthsAux_length`,
`finestGapWidths_length`, `wallTagCount_pushoutPathTags`, `finestGapWidths_pushoutPathTags_length`), the general
dom↔cod slot invariant (`finestGapWidths_slotCount_domCod_eq`), the canonical `id nil` factorization
(`pushoutFactorizeIdCanonicalNil`) and its spec probe, the per-class `rfl` probes, and the honesty / JAM A re-audit
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallTagCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidthsAux_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallTagCount_pushoutPathTags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_pushoutPathTags_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_slotCount_domCod_eq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeIdCanonicalNil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idCanonicalNilSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestSlotCount_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestSlotCount_wallWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestSlotCount_wallGapWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallCanonicalSlotCountAgrees
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCanonicalFiringBlockSlotSpec
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalReaderJamANarrowed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_firingBlockProducerStaysWalled

end FX1PolyAudit
