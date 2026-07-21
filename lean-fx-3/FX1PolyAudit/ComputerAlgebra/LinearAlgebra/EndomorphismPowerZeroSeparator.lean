import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismPowerZeroSeparator

/-! # EndomorphismPowerZeroSeparator — zero-axiom gate

Per-declaration zero-axiom gate for the rank-sequence (power-vanishing) separator: the
integer-cancellation lemmas, the matrix-power ladder, the witness transport/reflection of
power-vanishing, the `EndomorphismDissimilarByRankSequence` predicate and its witness-refutation, and
the Jordan-block-size grounding instances.

The design avoids abstract rank invariance: it transports power-vanishing across the concrete
similarity witness (`P · Q = d · I`, `Q · A · P = d · B`), so the separation is a per-input certificate.
Confirms freedom from `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The integer-cancellation substrate (the `1 + n` bridge is a clean `Nat.add_comm`).
#assert_no_axioms FX1Poly.ComputerAlgebra.intFactorIsZeroOfScaledZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intFactorIsZeroOfPowerScaledZero

-- The matrix-power ladder + its shape lemmas.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMatrixPower
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMatrixPowerRowCount
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMatrixPowerSuccColCount
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismWitnessPowerLadder

-- The witness transport/reflection of power-vanishing (the conjugation-invariance heart).
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismPowerVanishesOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismWitnessTransportsPowerVanishing
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismWitnessReflectsPowerVanishing

-- The dimension-coherence guard on the witness checker.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismDimensionForgeryPassesRawChecker
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismDimensionForgeryRejectedWithCoherence
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismShippedWitnessesPassCoherentChecker

-- The rank-sequence separator predicate + its witness-refutation.
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismDissimilarByRankSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismDissimilarByRankSequenceSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRankSequenceSeparationRefutesWitness

-- The Jordan-block-size grounding instances (equal char-poly, separated at the square).
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismZeroVersusJordanSeparatedByRankSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSplitVersusFullJordanSeparatedAtSquare
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSplitVersusFullJordanShareCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSplitVersusFullJordanNoWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismFullVersusSplitJordanNoWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanTwoTwoVersusThreeOneSeparatedAtSquare
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanTwoTwoVersusThreeOneNoWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanThreeOneVersusTwoTwoNoWitness

end FX1PolyAudit
