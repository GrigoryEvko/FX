import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorGates

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorGatesAudit — zero-axiom gate for the
matrix-algebra gates (a)/(b) + the K1 generic extractor (WP-PROP r13, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms` on
GATE (a), GATE (b), the K1 extractor, the matrix extensionality, and the shipped markers.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- W — the well-formedness kit.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListLengthAppend
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeMapMatWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityMatWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigma2x2WellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumWellFormed

-- Matrix extensionality by entries.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatExtByEntries

-- A-ARITH — the shift arithmetic + swapValue bounds.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidReassembleAboveTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidShiftBeqCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSubTwoBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapValueGeOfGe
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidTwoLeSubOfAdd

-- GATE (a) + GATE (b).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTransposition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulColumnSwapLaw

-- K1 prerequisites + K1.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixOfRangeIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwapEntryBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFoldlApplyAdjacentSwapEntryBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordEntriesBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordExtractor

-- The r13 markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMatrixGatesAndK1PrereqsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericPermMatrixExtractorK1Shipped

-- The FLIPPED wall marker (now = true; a Bool def is axiom-free either way).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit

-- Independent (non-fuel) axiom prints on the load-bearing gates, the extractor, extensionality, and the markers.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTransposition
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulColumnSwapLaw
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordExtractor
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatExtByEntries
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidShiftBeqCancel
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordEntriesBelow
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericPermMatrixExtractorK1Shipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit

end FX1PolyAudit
