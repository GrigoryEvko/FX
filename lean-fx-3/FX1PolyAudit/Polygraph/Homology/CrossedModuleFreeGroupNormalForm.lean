import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupNormalForm

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupNormalForm — zero-axiom gate (the group-
    enrichment of the pre-crossed carrier, the residue-keyed normal-form kit, and the injectivity/iso
    adjudication for the free crossed module of `⟨s | s³⟩`)

Per-declaration zero-axiom gate for WP-2GROUP r4 (#2199): the truth-probe on the two-letter identity
(B1), the group-enrichment congruence `FreeCrossedModuleEquiv` with its soundness extension and the two
clean self-attacks (B1), the residue-keyed sort/measure normal-form kit (B2), and the retargeted
injectivity/iso ledger (B3/B4).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.moralCounterexampleImageIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.moralCounterexampleBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.FreeCrossedModuleEquiv
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddRightNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddLeftNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.consInvCancelImage
#assert_no_axioms FX1Poly.Polygraph.Homology.invConsCancelImage
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageRespectsFreeCrossed
#assert_no_axioms FX1Poly.Polygraph.Homology.moralCounterexampleReducesUnderEnrichment
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityNotFreeCrossedTrivial
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedSandwichCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackOneBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackOneImageIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackOneReduces
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackThreeBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackThreeImageIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.selfAttackThreeReduces

end FX1PolyAudit
