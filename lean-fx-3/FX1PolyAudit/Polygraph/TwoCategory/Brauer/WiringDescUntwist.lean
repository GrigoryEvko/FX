import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwist

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescUntwist — zero-axiom gate (WP-BRAUER-4 r3)

Per-declaration zero-axiom gate for the seven-relation extension: the additive over-approximation `BrauerConvFree7`
(embedding `BrauerConvFree` via `ofFree` plus the two untwist rows), the non-vacuity witnesses, the r2 wall
DISSOLUTION (`crossingParity` no longer a `BrauerConvFree7` invariant), the extended-conv soundness witnesses (each
untwist whiskered in arbitrary context, via the keystone), and the three honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the seven-relation over-approximation + its additive embedding
#assert_no_axioms FX1Poly.Polygraph.BrauerConvFree7
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_ofFree

-- non-vacuity: the two untwists are derivable, and the old closure embeds
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_cupUntwist_derivable
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_capUntwist_derivable
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_crossingInvolution_seed

-- the r2 wall DISSOLUTION
#assert_no_axioms FX1Poly.Polygraph.crossingParity_not_brauerConvFree7_invariant
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_strictly_extends_brauerConvFree

-- extended-conv soundness: each untwist whiskered in arbitrary context
#assert_no_axioms FX1Poly.Polygraph.brauerConv_cupUntwist_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_capUntwist_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_untwist_inWiderContext_distinct

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerUntwistWallDissolved
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSevenRelationConvSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerStraighteningNFResidual

end FX1PolyAudit
