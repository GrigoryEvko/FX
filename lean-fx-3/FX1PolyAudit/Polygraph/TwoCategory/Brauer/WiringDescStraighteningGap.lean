import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraighteningGap

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStraighteningGap — zero-axiom gate (WP-BRAUER-4 r2 WALL)

Per-declaration zero-axiom gate for the free-straightening UNDER-GENERATION wall: the propext-free Boolean parity
(`boolXor` + laws), the crossing-count parity (`crossingParity` + append / pair / shift lemmas), the honest
over-approximation `BrauerConvFree` with its invariance theorem, the per-relation parity-soundness witnesses, the
non-vacuity witnesses, and the wall itself (`brauerUntwist_diagramEq` / `brauerUntwist_isBrauerConv` /
`brauerUntwist_parity_ne` / `brauerUntwist_not_brauerConvFree`) plus the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- propext-free Boolean parity
#assert_no_axioms FX1Poly.Polygraph.boolXor
#assert_no_axioms FX1Poly.Polygraph.boolXor_false_right
#assert_no_axioms FX1Poly.Polygraph.boolXor_comm
#assert_no_axioms FX1Poly.Polygraph.boolXor_assoc

-- the crossing-count parity + its structural lemmas
#assert_no_axioms FX1Poly.Polygraph.arcsAreCrossing
#assert_no_axioms FX1Poly.Polygraph.isCrossingWiring
#assert_no_axioms FX1Poly.Polygraph.isCrossingAtom
#assert_no_axioms FX1Poly.Polygraph.crossingParity
#assert_no_axioms FX1Poly.Polygraph.crossingParity_append
#assert_no_axioms FX1Poly.Polygraph.crossingParity_pair
#assert_no_axioms FX1Poly.Polygraph.shiftAtom
#assert_no_axioms FX1Poly.Polygraph.shiftWord
#assert_no_axioms FX1Poly.Polygraph.isCrossingAtom_shiftAtom
#assert_no_axioms FX1Poly.Polygraph.crossingParity_shiftWord

-- the honest over-approximation + invariance
#assert_no_axioms FX1Poly.Polygraph.BrauerConvFree
#assert_no_axioms FX1Poly.Polygraph.crossingParity_brauerConvFree

-- per-relation parity soundness
#assert_no_axioms FX1Poly.Polygraph.crossingParity_snake_sound
#assert_no_axioms FX1Poly.Polygraph.crossingParity_snakeMirror_sound
#assert_no_axioms FX1Poly.Polygraph.crossingParity_crossingInvolution_sound
#assert_no_axioms FX1Poly.Polygraph.crossingParity_yangBaxter_sound
#assert_no_axioms FX1Poly.Polygraph.crossingParity_capSlide_sound

-- non-vacuity
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree_crossingInvolution_seed
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree_yangBaxter_seed

-- the wall
#assert_no_axioms FX1Poly.Polygraph.brauerUntwist_diagramEq
#assert_no_axioms FX1Poly.Polygraph.brauerUntwist_isBrauerConv
#assert_no_axioms FX1Poly.Polygraph.brauerUntwist_parity_ne
#assert_no_axioms FX1Poly.Polygraph.brauerUntwist_not_brauerConvFree

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerStraighteningGap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingParityInvariant

end FX1PolyAudit
