import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.SemilatticeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingSemilattice.SemilatticeSeed — zero-axiom gate (the FULLY DECIDED walking bounded semilattice, single generator)

Per-declaration zero-axiom gate for the walking bounded semilattice: the `SemilatticeTree` carrier, the
two-valued `SlotPresence` invariant + its `slotJoin` algebra (assoc / comm / self / absent-right), the
`slotPresenceOf` fold + smokes, the `SemilatticeTreeConv` five-law convertibility, soundness, the `normalOf`
normal form, the four-case `semilatticeMulNormal`, normalization, completeness, the decision biconditional,
the idempotency / positive-decision / negative-decision groundings, and the marker.  The whole decision must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the two-valued model is
a purpose-built type whose join algebra is plain case-analysis, avoiding `Bool`/`decide`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SemilatticeTree
#assert_no_axioms FX1Poly.Polygraph.SlotPresence
#assert_no_axioms FX1Poly.Polygraph.slotJoin
#assert_no_axioms FX1Poly.Polygraph.slotJoinAssoc
#assert_no_axioms FX1Poly.Polygraph.slotJoinComm
#assert_no_axioms FX1Poly.Polygraph.slotJoinSelf
#assert_no_axioms FX1Poly.Polygraph.slotJoinAbsentRight
#assert_no_axioms FX1Poly.Polygraph.slotPresenceOf
#assert_no_axioms FX1Poly.Polygraph.slotPresenceOf_leaf
#assert_no_axioms FX1Poly.Polygraph.slotPresenceOf_unit
#assert_no_axioms FX1Poly.Polygraph.SemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.semilatticeTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.normalOf
#assert_no_axioms FX1Poly.Polygraph.semilatticeMulNormal
#assert_no_axioms FX1Poly.Polygraph.semilatticeTreeReducesToNormal
#assert_no_axioms FX1Poly.Polygraph.semilatticeTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.semilatticeTreeConv_iff_slotPresence
#assert_no_axioms FX1Poly.Polygraph.semilatticeIdemHolds
#assert_no_axioms FX1Poly.Polygraph.semilatticeDecidesEqualPresence
#assert_no_axioms FX1Poly.Polygraph.semilatticeRejectsUnequalPresence
#assert_no_axioms FX1Poly.Polygraph.fxWalkingSemilattice_hasSingleGeneratorDecision

end FX1PolyAudit
