import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingCupSwapRootComm

/-! # FX1PolyAudit/…/MatchingCupSwapRootComm — zero-axiom gate

Per-declaration zero-axiom gate for the Track B FINAL CRUX: the cup-restricted `rootComm` — the 4-id block
transposition `blockSwap nf` (`nf ↔ nf+2`, `nf+1 ↔ nf+3`) is a union-find AUTOMORPHISM of the two-fresh-join
graph `(nf+2,nf+3) :: (nf,nf+1) :: orig` over any fresh forest `orig`.  This is the CUP restriction of the
machine-refuted general `MatchingGodementCoreSwapSim.rootComm` (refuted only for the cap/merge case).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockSwap
#assert_no_axioms FX1Poly.Polygraph.blockSwap_fix_lt
#assert_no_axioms FX1Poly.Polygraph.blockSwap_nf
#assert_no_axioms FX1Poly.Polygraph.blockSwap_nf1
#assert_no_axioms FX1Poly.Polygraph.blockSwap_nf2
#assert_no_axioms FX1Poly.Polygraph.blockSwap_nf3
#assert_no_axioms FX1Poly.Polygraph.blockSwap_involutive
#assert_no_axioms FX1Poly.Polygraph.blockSwap_injective
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_map_of_parentComm
#assert_no_axioms FX1Poly.Polygraph.blockSwap_rootComm
#assert_no_axioms FX1Poly.Polygraph.blockRotate_two_two_eq_blockSwap
#assert_no_axioms FX1Poly.Polygraph.blockRotate_two_two_rootComm

end FX1PolyAudit
