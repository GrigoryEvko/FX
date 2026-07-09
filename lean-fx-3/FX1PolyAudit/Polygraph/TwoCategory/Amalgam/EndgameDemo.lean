import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.EndgameDemo

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.EndgameDemo — zero-axiom gate for the Tier-A capstone
(ENDGAME-DEMO r1, #2215)

Per-declaration zero-axiom gate for the whole capstone: the two demo-dimension presentations (D1 —
`protocolDualityComputad` / `stagedComputationComputad` + its reflected cells and law rows / the row-aware
fingerprints / the negative control), the gate-run recognition payoffs (D2), the decisions through the registry
families (D3 — the thin verdict + its cells, the sibling 1-cell separation, the row-aware both-verdicts), and the
capstone marker (D5).

TWO independent gates run on every declaration:

  * `#assert_no_axioms` — the project's fuel-based transitive-closure audit macro (throws on any `propext`,
    `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`).
  * `#print axioms` — the INDEPENDENT Lean-kernel axiom report on the payoffs + the capstone marker (the real gate:
    it reports the kernel's own dependency set, not the macro's fuel-bounded walk).  A clean payoff prints
    "does not depend on any axioms". -/

namespace FX1PolyAudit

-- D1: the two demo-dimension presentations (fresh-named data)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.protocolDualityComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.stagedCodeWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedQuote
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedIdCode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.stagedComputationComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.stagedComputationLawRows
#assert_no_axioms FX1Poly.Polygraph.Amalgam.stagedRowAware
#assert_no_axioms FX1Poly.Polygraph.Amalgam.partialStagingLawRows
#assert_no_axioms FX1Poly.Polygraph.Amalgam.partialStagingRowAware

-- D2: the gate runs — recognition from data + the negative control
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoProtocol_recognizedByRegistry
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoStaging_matchesMonadData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoStaging_distinctFromIdempotent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoUnregistered_rejected

-- D3: the decisions through the registry families
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoProtocol_admitted
#assert_no_axioms FX1Poly.Polygraph.Amalgam.protocolDualityNilCellA
#assert_no_axioms FX1Poly.Polygraph.Amalgam.protocolDualityNilCellB
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoProtocolThinVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoProtocolThinVerdict_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoProtocolDualSeparates
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoStaging_admitsMonad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoStagingBothVerdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.demoStagingBothVerdicts_holds

-- D5: the capstone marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxEndgame_hasTierADemo

/-! ## Independent kernel gate — `#print axioms` on the nine payoffs + the capstone marker

Not the fuel-based macro: the Lean kernel's own axiom report.  Each clean payoff prints
"does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Amalgam.demoProtocol_recognizedByRegistry
#print axioms FX1Poly.Polygraph.Amalgam.demoProtocol_admitted
#print axioms FX1Poly.Polygraph.Amalgam.demoProtocolThinVerdict_holds
#print axioms FX1Poly.Polygraph.Amalgam.demoProtocolDualSeparates
#print axioms FX1Poly.Polygraph.Amalgam.demoStaging_matchesMonadData
#print axioms FX1Poly.Polygraph.Amalgam.demoStaging_distinctFromIdempotent
#print axioms FX1Poly.Polygraph.Amalgam.demoStaging_admitsMonad
#print axioms FX1Poly.Polygraph.Amalgam.demoUnregistered_rejected
#print axioms FX1Poly.Polygraph.Amalgam.demoStagingBothVerdicts_holds
#print axioms FX1Poly.Polygraph.Amalgam.fxEndgame_hasTierADemo

end FX1PolyAudit
