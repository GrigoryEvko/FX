import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTotalRegionDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTotalRegionDispatch — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r42 total region dispatch: BRIDGE 1 (the exact→cap-free bridge
`capFreeRight_of_regionArrivedExact` with its two helpers), the two BRIDGE-1-gated arrival providers
(`outcomeArrivedFactoredStraddleSink` / `outcomeArrivedFactoredCrossingLeft`), the constructive-scope assembly
(`scopeWord` / `totalDispatch`) with its fate / classifier / measure probes, the cupless-prefix whiskering
(`prependCuplessPrefixArrived` / `prependCuplessPrefixAnnihilated` and the prefixed dispatch), the honesty markers, and
the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — BRIDGE 1 is structural on the
suffix via the r41 `andEqTrue_*` `&&`-split (`Bool.and_eq_true` leaks `propext`) + `Nat.eq_of_beq_eq_true`, the dispatch
is structural on the descriptor folding into the r40/r41 nested-structural providers, and the prefix whisker uses
`countAtoms_append` (never `List.append_assoc` / `Nat.sub_*`).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.outputCount_two_of_isCrossing
#assert_no_axioms FX1Poly.Polygraph.hasNoCap_of_allSettledLeftOfCup
#assert_no_axioms FX1Poly.Polygraph.capFreeRight_of_regionArrivedExact
#assert_no_axioms FX1Poly.Polygraph.outcomeArrivedFactoredStraddleSink
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_settledCrossingRight
#assert_no_axioms FX1Poly.Polygraph.outcomeArrivedFactoredCrossingLeft
#assert_no_axioms FX1Poly.Polygraph.scopeWord
#assert_no_axioms FX1Poly.Polygraph.totalDispatch
#assert_no_axioms FX1Poly.Polygraph.totalDispatch_fates
#assert_no_axioms FX1Poly.Polygraph.totalDispatch_classifierTie
#assert_no_axioms FX1Poly.Polygraph.totalDispatch_continueMeasureDescends
#assert_no_axioms FX1Poly.Polygraph.suffixRightOfFirstCup_prefixCupless
#assert_no_axioms FX1Poly.Polygraph.cupIsCapFreeRight_prefixCupless
#assert_no_axioms FX1Poly.Polygraph.prependCuplessPrefixArrived
#assert_no_axioms FX1Poly.Polygraph.prependCuplessPrefixAnnihilated
#assert_no_axioms FX1Poly.Polygraph.totalDispatchArrivedUnderPrefix
#assert_no_axioms FX1Poly.Polygraph.totalDispatchArrivedUnderPrefix_fate
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTotalRegionDispatchAssembly
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatRegionDispatchSynthesis
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_totalRegionDispatchTerminalState

end FX1PolyAudit
