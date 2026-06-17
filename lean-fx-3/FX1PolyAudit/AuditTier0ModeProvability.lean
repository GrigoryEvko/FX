import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Provability

/-! # FX1PolyAudit/AuditTier0ModeProvability — zero-axiom gate for mode-23

Per-declaration zero-axiom gate for `mode-23` (`FX1Poly/Tier0/Mode/Provability.lean`): the `□`/`◇` modalities + the
GL frame conditions, the normal modal core (K / necessitation / monotonicity / De Morgan), the 4 axiom, the LÖB
axiom (by well-founded induction), the polymodal `[n]` family + the GLP level-monotonicity, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  In particular the `Acc`-induction Löb proof must stay axiom-clean. -/

namespace FX1PolyAudit

-- Frames + modalities
#assert_no_axioms FX1Poly.Tier0.boxOver
#assert_no_axioms FX1Poly.Tier0.diamondOver
#assert_no_axioms FX1Poly.Tier0.IsTransitiveFrame
#assert_no_axioms FX1Poly.Tier0.ConverseWellFounded

-- The normal modal core (any frame)
#assert_no_axioms FX1Poly.Tier0.boxOver_distrib
#assert_no_axioms FX1Poly.Tier0.boxOver_necessitation
#assert_no_axioms FX1Poly.Tier0.boxOver_monotone
#assert_no_axioms FX1Poly.Tier0.diamondOver_not_boxOver_not

-- The 4 axiom + the LÖB axiom
#assert_no_axioms FX1Poly.Tier0.boxOver_four
#assert_no_axioms FX1Poly.Tier0.boxOver_loeb

-- The polymodal [n] family (GLP)
#assert_no_axioms FX1Poly.Tier0.boxAt
#assert_no_axioms FX1Poly.Tier0.boxAt_monotone_level
#assert_no_axioms FX1Poly.Tier0.boxAt_loeb

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGlpOrdinalAnalysis
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArithmeticalCompleteness
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKripkeCompleteness
#assert_no_axioms FX1Poly.Tier0.fxMode_hasReflectionCalculus
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelProvabilityFibration

end FX1PolyAudit
