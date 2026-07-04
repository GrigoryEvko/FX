import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexInjectivity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapReindexInjectivity — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head reindexing's injectivity atom (peel campaign
H, seed rung, cap links-leg atoms, part 2): propositional injectivity by direct zone-pair
analysis, and the Bool beq correspondence (the pointwise hypothesis of the join-transport kit
at the cap seed).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_injective
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_beqCorr

end FX1PolyAudit
