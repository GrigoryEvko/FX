import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKitAudit — zero-axiom gate for the
matrix-algebra kit gating the GENERIC permutation-matrix extractor: the shared relabel keystone (RELABEL-GET), the
generic list-algebra (map-form, length preservation, gate (c) cons-relabel), and the boundary-excluding valid-word
predicate (WP-PROP r12, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms` on
RELABEL-GET, its map-form, gate (c), the three swap-reads, and the marker.  The project `#assert_no_axioms` macro is
fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- K0 — the shared relabel keystone.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetConsSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapAtK
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapAtKSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapElsewhere
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapValueAtK
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapValueAtKSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapValueElsewhere
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetApplyAdjacentSwapRange
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapSwapValueRangeIsAdjacentSwap

-- K-list — length preservation of the fold, permOfWord length, and gate (c).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFoldlApplyAdjacentSwapLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordConsRelabel

-- K-valid — the boundary-excluding Bool predicate + peels.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPositionsValid
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAndSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPositionsValidHead
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPositionsValidTail

-- The r12 KIT (part 1) marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMatrixKitRelabelKeystoneShipped

-- Independent (non-fuel) axiom prints on RELABEL-GET, its map-form, gate (c), the three swap-reads, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetApplyAdjacentSwapRange
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapSwapValueRangeIsAdjacentSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordConsRelabel
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapAtK
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapAtKSucc
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetSwapElsewhere
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordLength
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMatrixKitRelabelKeystoneShipped

end FX1PolyAudit
