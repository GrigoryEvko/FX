import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellGodementIndependence

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellGodementIndependence — zero-axiom gate (mode-3 floor, Godement arc residual)

Per-declaration zero-axiom gate for the Godement arc-extract independence REDUCED to the two-block commutation
core: the fold-decomposition engine (`runArcCell` / `processArcSpine_spineDiff`), the sharpened residual
`ArcGodementCommute`, the reduction `arcGodementInvariant_of_commute` (the residual implies the parent's full
`godementInvariant`), the re-gated full `arcStructureOf` soundness `arcStructureOf_sound_of_arcGodementCommute`,
and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the fold-decomposition engine
#assert_no_axioms FX1Poly.Tier0.runArcCell
#assert_no_axioms FX1Poly.Tier0.processArcSpine_spineDiff

-- the sharpened two-block commutation residual
#assert_no_axioms FX1Poly.Tier0.ArcGodementCommute

-- the reduction + the re-gated full soundness
#assert_no_axioms FX1Poly.Tier0.arcGodementInvariant_of_commute
#assert_no_axioms FX1Poly.Tier0.arcStructureOf_sound_of_arcGodementCommute

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementFoldDecomposition
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementReducedToBlockCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcBlockCommuteProof

end FX1PolyAudit
