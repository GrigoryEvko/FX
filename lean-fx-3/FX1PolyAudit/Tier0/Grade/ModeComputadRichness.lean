import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Grade.ModeComputadRichness

/-! # FX1PolyAudit/Tier0/Mode/ModeComputadRichness — zero-axiom gate

Per-declaration zero-axiom gate for the carrier-computed richness leaf: `rungOfComputad` reading the finite
`ModeComputad` carrier, the landed `richnessOfComputad` / `richnessScalarOfComputad`, the concrete rung
read-offs, the CARRIER-COMPUTED crossover (superseding the evidence-threaded one), and the gap-closure
theorems proving the computed richness equals the v2 hand-supplied evidence.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The carrier-computed classifier + landing
#assert_no_axioms FX1Poly.Tier0.rungOfComputad
#assert_no_axioms FX1Poly.Tier0.richnessOfComputad
#assert_no_axioms FX1Poly.Tier0.richnessScalarOfComputad
#assert_no_axioms FX1Poly.Tier0.rungOfSpectrum_richnessOfComputad

-- Concrete rung read-offs
#assert_no_axioms FX1Poly.Tier0.singleObjectSemiringComputad_rung_r2
#assert_no_axioms FX1Poly.Tier0.adjunctionComputad_rung_r5

-- ★★★ The carrier-computed crossover
#assert_no_axioms FX1Poly.Tier0.crossover_computad_semiring_below_adjunction
#assert_no_axioms FX1Poly.Tier0.crossover_reads_modeCount
#assert_no_axioms FX1Poly.Tier0.crossover_computad_scalar_strictMono

-- The gap-closure
#assert_no_axioms FX1Poly.Tier0.adjunctionComputad_matches_evidence
#assert_no_axioms FX1Poly.Tier0.singleObjectSemiringComputad_matches_evidence
#assert_no_axioms FX1Poly.Tier0.adjunctionComputad_richnessEvidence_matches

-- Honesty marker
#assert_no_axioms FX1Poly.Tier0.fxMode_hasComputadRichness

end FX1PolyAudit
