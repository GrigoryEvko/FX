import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.DesignLock

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.DesignLock — zero-axiom gate for the POLY-TAB design lock + the
strategy-table mechanism tag (POLY-TAB r0, T2).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.DecisionMechanism
#assert_no_axioms FX1Poly.Polygraph.Table.decisionMechanism_thinLocallyThin_ne_undecidableWall
#assert_no_axioms FX1Poly.Polygraph.Table.frobeniusSpiderMechanism
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_hasDesignLock
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_contextClosureIsOptionII

end FX1PolyAudit
