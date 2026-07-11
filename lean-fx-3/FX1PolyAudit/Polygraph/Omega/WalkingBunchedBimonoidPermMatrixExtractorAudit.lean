import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractor

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorAudit — zero-axiom gate for the
permutation-matrix read-off: the pure `List Nat` symmetric-group engine, the permutation matrix, the
`sigmaAt`-as-transposition pins, the matMul column-swap law, the concrete extractor
(`evalCell (permWord w width) = permMatrixOf width (permOfWord w width)`), and the r11-pair reduction (WP-PROP r11,
#2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms`
on the extractor pins, the matMul column-swap law, the derived r11-pair matrix-share, and the separation.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- B1 — the pure engine + the permutation matrix.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidApplyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWord
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapValue
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixOf

-- B1.A — the sigmaAt-as-transposition pins.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTranspositionThreeZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTranspositionThreeOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTranspositionFourOne

-- B1.B — the matMul column-swap law pins.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulColumnSwapLawThreeZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulColumnSwapLawFourTwo

-- B1.C — the extractor pins.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorBraidThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorBraidThreeOther
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorFour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorFiveUnifyLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorFiveUnifyRight

-- B1.D — the r11-pair reduction + the separation.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidR11PairPermShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidR11PairMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordSeparatesOrder

-- The B1 marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMatrixExtractorCarrierAndPinsShipped

-- B2.A — the propext-clean Nat-beq bridges.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatBeqSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatEqOfBeqTrue

-- B2.B — list extensionality + the append / range indexers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListExtByGet
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetAppendLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetAppendSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAppendSnocCons
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeLoopAppend
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeLoopLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetRange

-- B2.C — natListGet / rowListGet commute with map.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetMapNat
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetMapRow

-- B2.D — the entry formula + the injective read-off.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixEntryAt
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixInjective

-- B2.E — the clean generic list-algebra.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapApplyAdjacentSwapCommute
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFoldlApplyAdjacentSwapMapCommute

-- The B2 marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMatrixInjectiveReadOffShipped

-- Independent (non-fuel) axiom prints on the extractor pins, the matMul law, the derived r11 matrix-share, and
-- the separation.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorBraidThree
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorFiveUnifyLeft
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidExtractorFiveUnifyRight
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulColumnSwapLawFourTwo
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtIsTranspositionFourOne
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidR11PairMatrixShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidR11PairPermShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermOfWordSeparatesOrder

-- Independent (non-fuel) axiom prints on the generic injective read-off, the entry formula, the range indexer,
-- and the clean list-algebra.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixInjective
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMatrixEntryAt
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGetRange
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapApplyAdjacentSwapCommute
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFoldlApplyAdjacentSwapMapCommute
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatEqOfBeqTrue

end FX1PolyAudit
