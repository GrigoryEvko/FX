import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.BicommutativeBimonoidPresentation

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.BicommutativeBimonoidPresentation — zero-axiom gate
(LAFONT-PROP r1, brick B: THE RELATION-DIFF GATE)

Per-declaration zero-axiom gate for the Lafont presentation of Mat(N) as the free bicommutative
bimonoid: the wire-diagram syntax, the matrix denotation, the generator-use counting machinery, THE FULL
18-ROW RELATION TABLE ([Lafont2003] figure 13 minus the Z2-specific row, plus the derivable right
(co)unit forms — 12 core bimonoid rows + 6 symmetry rows), the 18 per-row matrix-soundness fires, THE
RELATION-DIFF GATE (`relationDiffGatePasses` — inventory + soundness + the anti-Godement discriminators:
bare-identity retraction sides, swap-count asymmetry, total-overlap associativity shape, exact bialgebra
counts), the syntactic bare-identity pins, the presented congruence `AreConvertibleDiagrams` (structural
monoidal glue SEPARATE from the relation rows — interchange lives as glue, never as content), THE
DEFENSIVE FIRES (the exact r30 refuted unit pair and associativity pair, now one-step convertible, plus
the derived three-step chain), and the two named residual statements (congruence soundness,
completeness).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  All matches are full-enumeration over the eight constructors; all fires are kernel
`rfl` or single constructor applications.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.WireDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.singleWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapBesideWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireBesideSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addBesideWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireBesideAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyBesideWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireBesideCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardBesideWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireBesideDiscard
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroBesideWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireBesideZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyPairStage
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.innerSwapWindowStage
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addPairStage
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.denoteEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.GeneratorUseCounts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.noGeneratorUses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addGeneratorUseCounts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.countGeneratorUses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.hasGeneratorUseCounts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isGeneratorCell
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isBareIdentityDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isComposeEndingInGeneratorCell
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isComposeStartingWithGeneratorCell
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.LawFamilyTag
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lawFamilyCode
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.RelationRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isRowSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addAssociativityLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addAssociativityRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addAssociativityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addLeftUnitLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addLeftUnitRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addLeftUnitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addRightUnitLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addRightUnitRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addRightUnitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addCommutativityLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addCommutativityRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addCommutativityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCoassociativityLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCoassociativityRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCoassociativityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyLeftCounitLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyLeftCounitRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyLeftCounitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyRightCounitLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyRightCounitRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyRightCounitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCocommutativityLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCocommutativityRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCocommutativityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterAddLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterAddRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterAddBimonoidRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterZeroLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterZeroRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterZeroBimonoidRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterAddLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterAddRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterAddBimonoidRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterZeroLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterZeroRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterZeroBimonoidRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapInvolutionLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapInvolutionRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapInvolutionRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapYangBaxterLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapYangBaxterRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapYangBaxterRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastAddLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastAddRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastAddNaturalityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastZeroLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastZeroRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastZeroNaturalityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyPastSwapLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyPastSwapRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyPastSwapNaturalityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardPastSwapLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardPastSwapRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardPastSwapNaturalityRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lafontRelationRows
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addAssociativityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addLeftUnitRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addRightUnitRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addCommutativityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCoassociativityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyLeftCounitRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyRightCounitRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyCocommutativityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterAddBimonoidRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterZeroBimonoidRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterAddBimonoidRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterZeroBimonoidRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapInvolutionRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapYangBaxterRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastAddNaturalityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastZeroNaturalityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyPastSwapNaturalityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardPastSwapNaturalityRow_isSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areAllRowsSoundIn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.countRowsWithFamilyCode
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areAllRelationRowsSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doesRowInventoryMatchLafont
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areUnitRowsGenuineRetractions
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areCommutativityRowsSwapAsymmetric
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areAssociativityRowsTotalOverlap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.areBimonoidSquaresLafontExact
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doesRelationDiffGatePass
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.relationDiffGatePasses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.unitRowRightSidesAreBareIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.AreConvertibleDiagrams
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairMatchesAddRightUnitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairIsNowConvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairHasEqualMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mirrorUnitPairIsNowConvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairMatchesRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairIsNowConvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairHasEqualMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.derivedZeroThenLeftUnitChain
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.derivedZeroThenLeftUnitChainConverts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.convertibilityMatrixSoundnessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.matNatCompletenessStatement

end FX1PolyAudit
