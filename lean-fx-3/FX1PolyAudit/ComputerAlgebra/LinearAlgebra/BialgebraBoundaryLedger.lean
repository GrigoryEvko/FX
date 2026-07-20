import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.BialgebraBoundaryLedger

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/BialgebraBoundaryLedger —
    zero-axiom gate (WP-PROP-4: the bialgebra/Hopf boundary ledger)

Per-declaration zero-axiom gate for the bialgebra/Hopf boundary ledger over the
two committed linear-relation substrates (F2 phase-free ZX + IH_Q): the L1
SPECIAL fires (both calculi), the L2 FROBENIUS-vs-bialgebra split with the
cross-colour Frobenius refutation (`false` span pin + `Not ZxpConv` /
`Not IhzConv`), the L3 HOPF boundary (F2 identity antipode fires, Q identity
antipode FAILS, Q scalar-(-1) antipode holds), the L4 bicommutativity witnesses
and the owner-false non-commutative wall statement, and the L5 scalar cancel
boundary (k = 0 refuted, k != 0 holds), plus the ledger marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- L1 · SPECIAL
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialF2ZFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialF2XFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialF2ZConv
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialQWhiteFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialQBlackFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblSpecialQWhiteConv

-- L2 · FROBENIUS vs BIALGEBRA
#assert_no_axioms FX1Poly.ComputerAlgebra.wblFrobeniusF2SameColourFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblFrobeniusQSameColourFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblBialgebraF2CrossColourFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblBialgebraQCrossColourFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZxCrossColourFrobeniusLhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZxCrossColourFrobeniusRhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZxCrossColourFrobeniusFails
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZxCrossColourFrobeniusNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhCrossColourFrobeniusLhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhCrossColourFrobeniusRhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhCrossColourFrobeniusFails
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhCrossColourFrobeniusNotConv

-- L3 · HOPF
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHopfF2AntipodeIdentityFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHopfF2Conv
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhDiscardZero
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhHopfIdentityAntipodeLhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHopfQIdentityAntipodeFails
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHopfQIdentityAntipodeNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhHopfScalarAntipodeLhs
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHopfQScalarAntipodeFires

-- L4 · COMMUTATIVITY + non-commutative wall
#assert_no_axioms FX1Poly.ComputerAlgebra.wblCommutativityF2Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblCommutativityQFires
#assert_no_axioms FX1Poly.ComputerAlgebra.wblNoncommutativeWallStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.wblNoncommutativeWallIsProven

-- L5 · SCALAR cancel boundary
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhZeroScalarCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.wblIhWire
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZeroScalarCancelFails
#assert_no_axioms FX1Poly.ComputerAlgebra.wblZeroScalarCancelNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.wblNonzeroScalarCancelFires

-- marker
#assert_no_axioms FX1Poly.ComputerAlgebra.wblHasBoundaryLedger

end FX1PolyAudit
