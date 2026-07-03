import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapObstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingSwapObstruction — zero-axiom gate

Per-declaration zero-axiom gate for the two machine-checked refutations of the mode-3 keystone's standing
block-swap residual: the cup collision (non-fresh `openMap` failure) and the join-order root flip (fresh-state
ROOT-level `rootComm` failure), plus the freshness-conditioned variants they refute and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.not_matchingGodementCoreSwapSim
#assert_no_axioms FX1Poly.Tier0.MatchingGodementCoreSwapSimFresh
#assert_no_axioms FX1Poly.Tier0.not_matchingGodementCoreSwapSimFresh
#assert_no_axioms FX1Poly.Tier0.MatchingGodementSwapRenameableFresh
#assert_no_axioms FX1Poly.Tier0.not_matchingGodementSwapRenameableFresh
#assert_no_axioms FX1Poly.Tier0.not_matchingGodementSwapRenameable
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingCoreSwapObstructions

end FX1PolyAudit
