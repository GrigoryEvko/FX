import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithInvariantFactors

/-! # FX1PolyAudit/.../RationalPolynomialSmithInvariantFactors — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] Smith submatrix descent and the invariant-factor chain assembly.
Covers T1 (the descent driver `rsiDiagonalize` and its step equations), T2 (the per-stage all-zero-cross
correctness `rsiStageAllZeroCross`/`rsiDiagonalizeHeadAllZeroCross`), T3 (the chain assembly
`rsiHeadDividesAllOfConsecutive` via `rbzDividesTrans`), T5 (the `xI − A` characteristic-matrix constructor
`rsiCharMatrix`), plus the fires and content markers (including the two walls `rsiHasSmithNormalForm`,
`rsiHasRationalCanonicalForm`).

Every definition is structural on the `Nat` fuel or the list; every specification routes through the committed
driver/pivot-search/divisibility lemmas and calibrated-clean `Nat` order lemmas.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- T1 — the submatrix descent driver
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiStage
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiDiagonalize
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiDiagonalizeSuccNone
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiDiagonalizeSuccSome

-- T2 — per-stage all-zero-cross correctness
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiStageAllZeroCross
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiDiagonalizeHeadAllZeroCross

-- T3 — the invariant-factor chain assembly
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiConsecutiveDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHeadDividesAll
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiAnchorDividesAllOfConsecutive
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHeadDividesAllOfConsecutive

-- T5 — the xI − A characteristic-matrix constructor
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiCharCell
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiCharRowBuild
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiCharMatrixBuild
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiCharMatrix

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDiagMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDiagAlreadySmith
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDescentLength
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDescentDegrees
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireWrongDiagonalRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireStageAllZeroCross
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDiagConsecutiveDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireDiagHeadDividesAll
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiFireCharMatrix

-- Content markers and walls
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHasDescentDriver
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHasAllZeroCrossPerStage
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHasChainAssembly
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHasSmithNormalForm
#assert_no_axioms FX1Poly.ComputerAlgebra.rsiHasRationalCanonicalForm

end FX1PolyAudit
