import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSoundStar

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidMatrixSoundStarAudit — zero-axiom gate for Node A: the
`Mat(N)` strict-law matrix kit exercised at wide concrete witnesses and the strict-row-to-CONV-and-matrix bridge
(WP-PROP r27).

Per-declaration `#assert_no_axioms` on the wide witnesses + their well-formedness, the strict-law matrix
identities (vcompAssoc via `matMulAssoc`, vcompUnit via `identityRightUnit`, whisker-unit as directSum-of-
identities at three width-7 splits, whisker-functorial via `blockExchangeInterchange`, whisker-associator as
directSum-associativity), the strict-row-to-CONV-and-matrix bridge (both halves), and the delivery markers —
PLUS an independent (non-fuel) `#print axioms` on the same public declarations.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` closes the gate on the `Decidable.decide` reductions
(propext-free) and the shipped general lemma applications.  The wall markers
(`fxBunchedBimonoid_matrixStrictLawExtensionReached`, the star owner) stay `= false` byte-intact (cross-file, not
edited). -/

namespace FX1PolyAudit

-- A1 — the wide witnesses + their well-formedness.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWitnessWideA
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWitnessWideB
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWitnessWideC
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWitnessWideBWellFormed

-- A2 — vcompAssoc + vcompUnit in Mat(N) at wide (the shipped general lemmas invoked).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAVcompAssocWide
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAVcompUnitRightWide

-- A3 — whisker-unit in Mat(N) at three width-7 splits.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerUnitFourThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerUnitFiveTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerUnitSixOne

-- A4 — whisker-functorial (block exchange) + whisker-associator (directSum-assoc) at wide.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerFunctorialWide
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerAssocWide

-- A5 — the strict-row-to-CONV-and-matrix bridge (both halves).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeConvOverStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeMatrixShared

-- A6 — the delivery markers (incl. the walls that stay false).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAMatrixKitExercisedAtWideWitnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAStrictRowBridgeAtWideWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAUniversalAbsorberStillWalled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterNodeAWideKit
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_matrixSoundStarNodeARoundLedgerShipped

-- Independent (non-fuel) axiom prints on the same public declarations — closing the gate on the
-- `Decidable.decide` reductions (propext-free) and the shipped general-lemma applications.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWitnessWideBWellFormed
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAVcompAssocWide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAVcompUnitRightWide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerUnitSixOne
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerFunctorialWide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeAWhiskerAssocWide
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeConvOverStar
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNodeABridgeMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAMatrixKitExercisedAtWideWitnesses
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAStrictRowBridgeAtWideWitness
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAUniversalAbsorberStillWalled
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterNodeAWideKit
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_matrixSoundStarNodeARoundLedgerShipped

end FX1PolyAudit
