import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.MultiplierEndofunctor

/-! # FX1PolyAudit/AuditAxisModeMultiplierEndofunctor — zero-axiom gate for mode-12

Per-declaration zero-axiom gate for `mode-12` (`FX1Poly/Axis/Mode/MultiplierEndofunctor.lean`): the multiplier
endofunctor, the unpointability criterion (+ the mutual-exclusivity theorem), the dimensional-splitness
criterion, the combination witnesses, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The multiplier endofunctor + the dimension
#assert_no_axioms FX1Poly.Axis.Multiplier
#assert_no_axioms FX1Poly.Axis.Multiplier.dimension

-- The unpointability criterion + the dichotomy
#assert_no_axioms FX1Poly.Axis.Multiplier.IsPointed
#assert_no_axioms FX1Poly.Axis.Multiplier.IsUnpointable
#assert_no_axioms FX1Poly.Axis.Multiplier.not_pointed_and_unpointable

-- The dimensional-splitness criterion
#assert_no_axioms FX1Poly.Axis.Multiplier.SplitData
#assert_no_axioms FX1Poly.Axis.Multiplier.IsDimensionallySplit

-- The combination witnesses
#assert_no_axioms FX1Poly.Axis.identityMultiplier
#assert_no_axioms FX1Poly.Axis.identityMultiplier_isPointed
#assert_no_axioms FX1Poly.Axis.identityMultiplier_splitData
#assert_no_axioms FX1Poly.Axis.identityMultiplier_isSplit
#assert_no_axioms FX1Poly.Axis.voidMultiplier
#assert_no_axioms FX1Poly.Axis.voidMultiplier_isUnpointable
#assert_no_axioms FX1Poly.Axis.voidMultiplier_splitData
#assert_no_axioms FX1Poly.Axis.voidMultiplier_isSplit
#assert_no_axioms FX1Poly.Axis.functionMultiplier
#assert_no_axioms FX1Poly.Axis.functionMultiplier_isPointed

-- The NOT-split negative
#assert_no_axioms FX1Poly.Axis.squareMultiplier
#assert_no_axioms FX1Poly.Axis.squareMultiplier_isPointed
#assert_no_axioms FX1Poly.Axis.unitProd_subsingleton
#assert_no_axioms FX1Poly.Axis.bool_eq_of_ne_ne
#assert_no_axioms FX1Poly.Axis.squareMultiplier_not_split

-- Per-class realization: the cube interval endofunctor + operations + laws
#assert_no_axioms FX1Poly.Axis.intervalMultiplier
#assert_no_axioms FX1Poly.Axis.intervalMultiplier_isPointed
#assert_no_axioms FX1Poly.Axis.intervalDiagonal
#assert_no_axioms FX1Poly.Axis.intervalMeet
#assert_no_axioms FX1Poly.Axis.intervalJoin
#assert_no_axioms FX1Poly.Axis.intervalReversal
#assert_no_axioms FX1Poly.Axis.intervalMeet_diagonal
#assert_no_axioms FX1Poly.Axis.intervalMeet_comm
#assert_no_axioms FX1Poly.Axis.intervalReversal_deMorgan
#assert_no_axioms FX1Poly.Axis.intervalReversal_involutive
#assert_no_axioms FX1Poly.Axis.deMorgan_realizes_reversal

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasPerClassEndofunctorRealization
#assert_no_axioms FX1Poly.Axis.fxMode_hasNonSplitMultiplierProof
#assert_no_axioms FX1Poly.Axis.fxMode_hasPresheafMultiplierModel

end FX1PolyAudit
