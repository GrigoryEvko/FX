import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer

/-! # FX1PolyAudit/…/ArcPureCupTransfer — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cup transfer: the cap-first base-case guard
`capAtomCount firstList = 0` plus the whole-spine arc equality force `AllCupArity` on both spines
(the entry to the cup-interchange base case), with the converse `capAtomCount_ofAllCupArity` supplying
the clean `AllCupArity ↔ capAtomCount = 0` characterization.  The private `capCountReflect` is covered
transitively — a `propext` leak there would surface on the public theorems asserted here.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capAtomCount_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.cupAtomCount_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.bothPureCup_ofCapCountZeroAndArcEqual
#assert_no_axioms FX1Poly.Polygraph.pureCupSpines_sameLength_ofArcEqual
#assert_no_axioms FX1Poly.Polygraph.allCupArity_preservedOfAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.allCupArity_ofCons
#assert_no_axioms FX1Poly.Polygraph.pureCupSpine_internalCapCounts_eq_replicate
#assert_no_axioms FX1Poly.Polygraph.pureCupSpines_internalCapCountsAgree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPureCupTransfer

end FX1PolyAudit
