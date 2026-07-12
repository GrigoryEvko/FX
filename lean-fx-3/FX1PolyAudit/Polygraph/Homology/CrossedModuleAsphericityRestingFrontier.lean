import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleAsphericityRestingFrontier

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleAsphericityRestingFrontier — zero-axiom gate for the
    WP-2GROUP r10 honest resting adjudication (the crossed-module `π₂`-vs-`H₂` frontier)

Per-declaration zero-axiom gate: the frontier-status inductive `AsphericityFrontierStatus`, the resting
record `CrossedModuleAsphericityRestingFrontier` with its filled value, the two `rfl` star-pin theorems
(`h2CrossCheckStar` stays byte-identical — no fabricated flip), and the resting marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  The file is pure inductive / structure / `rfl`: no `Nat` arithmetic, no `List`, no `Beq`, hence
no polymorphic-recursion propext surface; the star-pin theorems compare literal enum constructors by
`rfl`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.AsphericityFrontierStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.CrossedModuleAsphericityRestingFrontier
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityRestingFrontier
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityStarStaysAtR9Residual
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityStarTopRowStaysShipped
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityWalkerRestsAtHonestFrontier

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
`#assert_no_axioms`; the core `#print axioms` command does not truncate). -/

#print axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityRestingFrontier
#print axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityStarStaysAtR9Residual
#print axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityStarTopRowStaysShipped
#print axioms FX1Poly.Polygraph.Homology.crossedModuleAsphericityWalkerRestsAtHonestFrontier

end FX1PolyAudit
