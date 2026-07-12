import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorExtractor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorExtractor — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r43 flat→descriptor EXTRACTOR (the r40 JAM D): the `Nat.ble`-to-`≤`
bridge + the crossing / cap / cup reconstruction primitives, the `recoverDistantIndex` boundary decoder with its
roundtrip, the Σ-bundled `extractDistantStep` / `extractDistantTail` with the decode roundtrip, the untwist-run peel with
its cons-only roundtrip, the head-cup `extractCupHead` / `extractWorkingRegion`, the flat synthesis `flatRegionDispatch`,
the firing / coverage probes, the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the roundtrips are cons-only
`rw` (no `List.append_assoc`), the disjointness `Prop` comes from `Nat.ble` via the hand-rolled `natLeOfBleExtract`, the
atom reconstruction is structure eta off the `DecidableEq WiringDesc` equality, and the transport is the r41 shipped
explicit-motive `Eq.rec` (`RegionCupOutcome.transportByRegionEq`).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natLeOfBleExtract
#assert_no_axioms FX1Poly.Polygraph.crossingAt_of_wiring
#assert_no_axioms FX1Poly.Polygraph.capAt_of_wiring
#assert_no_axioms FX1Poly.Polygraph.cupAt_of_wiring
#assert_no_axioms FX1Poly.Polygraph.recoverDistantIndex
#assert_no_axioms FX1Poly.Polygraph.recoverDistantIndex_roundtrip
#assert_no_axioms FX1Poly.Polygraph.extractDistantStep
#assert_no_axioms FX1Poly.Polygraph.extractDistantTail
#assert_no_axioms FX1Poly.Polygraph.extractDistantTail_decodes
#assert_no_axioms FX1Poly.Polygraph.isLeadingUntwistCrossing
#assert_no_axioms FX1Poly.Polygraph.atom_eq_crossingAt_of_isLeadingUntwist
#assert_no_axioms FX1Poly.Polygraph.untwistRunCount
#assert_no_axioms FX1Poly.Polygraph.untwistRunRemainder
#assert_no_axioms FX1Poly.Polygraph.untwistRun_roundtrip
#assert_no_axioms FX1Poly.Polygraph.extractCupHead
#assert_no_axioms FX1Poly.Polygraph.extractWorkingRegion
#assert_no_axioms FX1Poly.Polygraph.flatRegionDispatch
#assert_no_axioms FX1Poly.Polygraph.extractDistantTail_flagship
#assert_no_axioms FX1Poly.Polygraph.flatDispatch_firesOnHostiles
#assert_no_axioms FX1Poly.Polygraph.extractWorkingRegion_coverage
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatDescriptorExtractor
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatDescriptorSynthesisGap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_flatDescriptorExtractorTerminalState

end FX1PolyAudit
