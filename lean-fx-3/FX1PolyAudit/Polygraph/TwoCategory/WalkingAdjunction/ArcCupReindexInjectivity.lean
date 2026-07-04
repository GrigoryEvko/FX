import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexInjectivity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupReindexInjectivity — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head reindexing's injectivity atom (peel campaign
H, seed rung, links-leg atoms, part 2): propositional injectivity via the value-recovery left
inverse, and the Bool beq correspondence (the `componentCorr` hypothesis of the join-transport
kit at the cup seed).  The private recovery map and its left inverse are covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_injective
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_beqCorr

end FX1PolyAudit
