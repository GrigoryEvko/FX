import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.MultiplierEndofunctor

/-! # FX1PolyAudit/AuditTier0ModeMultiplierEndofunctor — zero-axiom gate for mode-12

Per-declaration zero-axiom gate for `mode-12` (`FX1Poly/Tier0/Mode/MultiplierEndofunctor.lean`): the multiplier
endofunctor, the unpointability criterion (+ the mutual-exclusivity theorem), the dimensional-splitness
criterion, the combination witnesses, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The multiplier endofunctor + the dimension
#assert_no_axioms FX1Poly.Tier0.Multiplier
#assert_no_axioms FX1Poly.Tier0.Multiplier.dimension

-- The unpointability criterion + the dichotomy
#assert_no_axioms FX1Poly.Tier0.Multiplier.IsPointed
#assert_no_axioms FX1Poly.Tier0.Multiplier.IsUnpointable
#assert_no_axioms FX1Poly.Tier0.Multiplier.not_pointed_and_unpointable

-- The dimensional-splitness criterion
#assert_no_axioms FX1Poly.Tier0.Multiplier.SplitData
#assert_no_axioms FX1Poly.Tier0.Multiplier.IsDimensionallySplit

-- The combination witnesses
#assert_no_axioms FX1Poly.Tier0.identityMultiplier
#assert_no_axioms FX1Poly.Tier0.identityMultiplier_isPointed
#assert_no_axioms FX1Poly.Tier0.identityMultiplier_splitData
#assert_no_axioms FX1Poly.Tier0.identityMultiplier_isSplit
#assert_no_axioms FX1Poly.Tier0.voidMultiplier
#assert_no_axioms FX1Poly.Tier0.voidMultiplier_isUnpointable
#assert_no_axioms FX1Poly.Tier0.voidMultiplier_splitData
#assert_no_axioms FX1Poly.Tier0.voidMultiplier_isSplit
#assert_no_axioms FX1Poly.Tier0.functionMultiplier
#assert_no_axioms FX1Poly.Tier0.functionMultiplier_isPointed

-- The NOT-split negative
#assert_no_axioms FX1Poly.Tier0.squareMultiplier
#assert_no_axioms FX1Poly.Tier0.squareMultiplier_isPointed
#assert_no_axioms FX1Poly.Tier0.unitProd_subsingleton
#assert_no_axioms FX1Poly.Tier0.bool_eq_of_ne_ne
#assert_no_axioms FX1Poly.Tier0.squareMultiplier_not_split

-- Per-class realization: the cube interval endofunctor + operations + laws
#assert_no_axioms FX1Poly.Tier0.intervalMultiplier
#assert_no_axioms FX1Poly.Tier0.intervalMultiplier_isPointed
#assert_no_axioms FX1Poly.Tier0.intervalDiagonal
#assert_no_axioms FX1Poly.Tier0.intervalMeet
#assert_no_axioms FX1Poly.Tier0.intervalJoin
#assert_no_axioms FX1Poly.Tier0.intervalReversal
#assert_no_axioms FX1Poly.Tier0.intervalMeet_diagonal
#assert_no_axioms FX1Poly.Tier0.intervalMeet_comm
#assert_no_axioms FX1Poly.Tier0.intervalReversal_deMorgan
#assert_no_axioms FX1Poly.Tier0.intervalReversal_involutive
#assert_no_axioms FX1Poly.Tier0.deMorgan_realizes_reversal

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasPerClassEndofunctorRealization
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNonSplitMultiplierProof
#assert_no_axioms FX1Poly.Tier0.fxMode_hasPresheafMultiplierModel

end FX1PolyAudit
