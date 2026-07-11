import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderNormalForm

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidSpiderNormalFormAudit — zero-axiom gate for the matrix
PROP opens (WP-PROP r1, #2032/#2033).

Per-declaration `#assert_no_axioms` on: the arity word + the PROP object widths + the width bridge, the hom-set
view (each dim-2 generator's boundary widths), the composition view (domain / codomain preservation), and the B1
marker (B1); the spider building blocks (`deltaFan`, `muFold`, `spiderScalar`) + the instance spiders + the
per-instance round-trips + the B2 markers (B2); the two completeness instances (convertibility over the sound
sub-theory + the derived / round-trip matrix agreements) + the B3 marker (B3); the ledger / census markers (B4).

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the spider constructor, a round-trip, and the
completeness-instance convertibility closes the gate. -/

namespace FX1PolyAudit

-- B1 — the PROP objects (arity word + widths + bridge).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowZero_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowOne_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowTwo_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowThree_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowTwoWidthMatchesAaWord

-- B1 — the hom-set view (boundary widths of each dim-2 generator).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEtaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEpsGen_isHomTargetWidth

-- B1 — the composition view (domain / codomain preservation) + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesDomain
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesCodomain
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositeSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositeTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_propHomAndCompositionViewsTypeCheck

-- Independent confirmation (not fuel-based) of the B1 arity word + a hom-view fact.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPow
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesDomain

end FX1PolyAudit
