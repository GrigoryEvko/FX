import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemBeyondCensusWitnessBundle

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.WordProblemBeyondCensusWitnessBundle — zero-axiom gate

Per-declaration zero-axiom gate for the beyond-census witness-bundle + cost-tag file (WP-LEDGER #2048
grand-ledger flip-bill item 1): the four decision/normal-form witness aliases, the three-rung decided
enumeration + count + exhaustiveness, the two total cost maps + their rows + the all-cited receipt, and the
discharge marker with its read-only grand-still-open coupling.

The `#assert_no_axioms` on the four aliases transitively certifies that the three beyond-census deciders
themselves (`decideBraidThreeGroupConv`, `decidableStringSaturatedConv_holds`, `decideBrauerConvBool`) and the
Brauer normal form (`classRepresentativeOf`) are zero-axiom.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four witness aliases (transitively certify the deciders + normal form are zero-axiom).
#assert_no_axioms FX1Poly.Polygraph.Table.wpBeyondBraidGroupDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpBeyondAdjointTripleStringDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpBeyondBrauerIndexedDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpBeyondBrauerClassRepresentative

-- The three-rung decided enumeration + count + exhaustiveness.
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusDecidedRungs
#assert_no_axioms FX1Poly.Polygraph.Table.beyondCensusDecidedRungCountIsThree
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusDecidedRungsExhaustive

-- The cost maps + rows + the all-cited receipt.
#assert_no_axioms FX1Poly.Polygraph.Table.beyondCensusDecidedCostClass
#assert_no_axioms FX1Poly.Polygraph.Table.beyondCensusDecidedCostEvidence
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusDecidedRungsCostClassRow
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusDecidedRungsCostEvidenceRow
#assert_no_axioms FX1Poly.Polygraph.Table.allBeyondCensusDecidedRungsCostEvidenceCited

-- The discharge marker + its read-only grand-still-open coupling.
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_hasThreeDecidedRungWitnessesAndCostTags
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpBeyond_decidedRungBillItemOneDischargedGrandStillOpen

end FX1PolyAudit
