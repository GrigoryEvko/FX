import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupArrivalPeel

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupArrivalPeel — zero-axiom gate

Per-declaration zero-axiom gate for the cup-ARRIVAL predicate (`suffixRightOfFirstCup` / `hasNoCap` /
`cupIsCapFreeRight` / `cupHasArrived` + the machine-checked probes), the GENERAL distant-tail single-cup PEEL
(`DistantSlideStep` / `distantStepAtom` / `distantTailWord` / `legPeelDistantTail` + the under-standard-prefix wrapper,
the r35-flagship re-derivation, the five-step demo, the fuel-floor bridge), and the STRADDLE terminal-cleanup rung
(`beq_self` / `straddleWindowBit_*` / `straddleSlideFree8_clean` / `straddleBitAtFirstCup_prefixCupless` /
`legFuel_leftmostCupStraddle_lt` / `legSink_cupStraddle_underStandardPrefix`), the honesty markers, and the
machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — note the stdlib
`Nat.beq_refl` LEAKS `propext` and is deliberately replaced by the structural `beq_self`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.suffixRightOfFirstCup
#assert_no_axioms FX1Poly.Polygraph.hasNoCap
#assert_no_axioms FX1Poly.Polygraph.cupIsCapFreeRight
#assert_no_axioms FX1Poly.Polygraph.cupHasArrived
#assert_no_axioms FX1Poly.Polygraph.cupArrival_probes
#assert_no_axioms FX1Poly.Polygraph.cupIsCapFreeRight_falsePositive
#assert_no_axioms FX1Poly.Polygraph.distantStepAtom
#assert_no_axioms FX1Poly.Polygraph.distantTailWord
#assert_no_axioms FX1Poly.Polygraph.legPeelDistantTail
#assert_no_axioms FX1Poly.Polygraph.legPeelDistantTail_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.legPeelToArrival_viaDistantTail_demo
#assert_no_axioms FX1Poly.Polygraph.legPeelDistantTail_len5_demo
#assert_no_axioms FX1Poly.Polygraph.legLexFuel_ofArrived_le_one
#assert_no_axioms FX1Poly.Polygraph.isCupAtom_false_of_hasNoCup_cons
#assert_no_axioms FX1Poly.Polygraph.hasNoCup_cons_tail
#assert_no_axioms FX1Poly.Polygraph.beq_self
#assert_no_axioms FX1Poly.Polygraph.beq_self_plus_two
#assert_no_axioms FX1Poly.Polygraph.straddleWindowBit_cupCrossingSucc
#assert_no_axioms FX1Poly.Polygraph.straddleWindowBit_cupSuccCrossing
#assert_no_axioms FX1Poly.Polygraph.straddleSlideFree8_clean
#assert_no_axioms FX1Poly.Polygraph.straddleBitAtFirstCup_prefixCupless
#assert_no_axioms FX1Poly.Polygraph.legFuel_leftmostCupStraddle_lt
#assert_no_axioms FX1Poly.Polygraph.legSink_cupStraddle_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupArrivalPredicate
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDistantTailCupPeel
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleTerminalCleanup
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSingleCupPeelDischarged
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_cupArrivalPeelTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.legPeelDistantTail
#print axioms FX1Poly.Polygraph.legFuel_leftmostCupStraddle_lt
#print axioms FX1Poly.Polygraph.cupArrival_probes
#print axioms FX1Poly.Polygraph.fxBrauer_cupArrivalPeelTerminalState

end FX1PolyAudit
