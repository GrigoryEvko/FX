import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkOrdered

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkOrdered — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r41 J-geometry ordered rewrite: the settled-crossing commutation via the
Godement interchange (`swapCrossingPastDistantStep` / `commuteSettledCrossingPastTail`), the exact-arrival read-off
(`regionArrivedExact_ofPeelSnoc`), the ordered sink-distant-before-straddle rewrite (`sinkDistantThenStraddle_arrives`)
and its r40-witness pin (`sinkDistantThenStraddle_arrivesWitness`), the honesty marker, and the machine-checked terminal
state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the `interchange`-transported
position `positionB - 2 + 2` reduces DEFINITIONALLY (no `Nat.sub` lemma), `List.cons_append` is definitional (no
`List.append_assoc`), and the structural tail recursion + `decide`-closed short-word pins are all axiom-free.  Registered
in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.swapCrossingPastDistantStep
#assert_no_axioms FX1Poly.Polygraph.commuteSettledCrossingPastTail
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_ofPeelSnoc
#assert_no_axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrives
#assert_no_axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrivesWitness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleSinkOrdered
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_straddleSinkOrderedTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.commuteSettledCrossingPastTail
#print axioms FX1Poly.Polygraph.regionArrivedExact_ofPeelSnoc
#print axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrives
#print axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrivesWitness
#print axioms FX1Poly.Polygraph.fxBrauer_straddleSinkOrderedTerminalState

end FX1PolyAudit
