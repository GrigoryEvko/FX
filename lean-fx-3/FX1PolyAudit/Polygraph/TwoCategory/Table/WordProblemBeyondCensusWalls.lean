import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemBeyondCensusWalls

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.WordProblemBeyondCensusWalls — zero-axiom gate

Per-declaration zero-axiom gate for the beyond-census walls tabulation (the WP-LEDGER #2048 owed piece):
the thirteen-rung enumeration, the count + exhaustiveness theorems, the disposition taxonomy + total map,
the recorded-disposition receipt, the ten per-rung live-flag `rfl` pins, and the summary markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The enumeration + counts + exhaustiveness.
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemBeyondCensusRungs
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemBeyondCensusRungCountIsThirteen
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemBeyondCensusRungsExhaustive

-- The disposition taxonomy + the total map + the receipt.
#assert_no_axioms FX1Poly.Polygraph.Table.beyondCensusDisposition
#assert_no_axioms FX1Poly.Polygraph.Table.hasRecordedDisposition
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusRungsHaveRecordedDisposition

-- The per-rung live-flag pins.
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingEquivalenceRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingFrobeniusMonadRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingStrongMonadRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingBunchedBimonoidRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingDistributiveLawRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_brauerCategoryRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingCohesionQuadrupleRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_adjointTripleStringRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_freeCrossedModuleTwoGroupRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_walkingEndomorphismLinearRungPinned
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_extensionWallsPinned

-- The summary markers.
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_beyondCensusWallsTabulated
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_tabulationLandedGrandStillOpen

end FX1PolyAudit
