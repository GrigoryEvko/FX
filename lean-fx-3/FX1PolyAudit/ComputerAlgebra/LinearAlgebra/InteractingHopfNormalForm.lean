import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalForm

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfNormalForm —
    zero-axiom gate (WP-PROP-3 brick 8: the move-past-block cascade denotation)

Per-declaration zero-axiom gate for the discharge of the brick-7 primary residual
`ihrMoveRightDenoteResidual`: the nil-cat rewrite helper (`ihnCatNilLeft`); the
move-pair structural predicate (`ihnMovePairSpec`); THE CASCADE DENOTATION
(`ihnMoveRightDenote`) and the residual inhabitant
(`ihnMoveRightDenoteResidualHolds`); the DECIDED marker (`ihnHasCascadeDenote`);
the kernel span fires with FALSE control and the content fire routing through the
theorem (`ihnFireMoveRightZeroTwoZero`, `ihnFireMoveRightZeroTwoZeroFalse`,
`ihnFireCascadeContent`); the perfect interleave (`ihnInterleave`); the faithful
(un)shuffle denotation statements (`ihnUnshuffleDenoteStatement`,
`ihnShuffleDenoteStatement`, owner false — they correct the under-specified
committed `ihrUnshuffleDenoteResidual`); the (un)shuffle span fires
(`ihnFireUnshuffleTwo`, `ihnFireUnshuffleTwoFalse`); the three owner-false markers
(`ihnHasUnshuffleDenote`, `ihnHasTwoRowSpatialSum`, `ihnHasNormalFormCompiler`).

No new inductives/structures are introduced, so there are no constructors,
`mk`, or projections to gate — every declaration is a `def` or `theorem`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihnCatNilLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnMovePairSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnMoveRightDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnMoveRightDenoteResidualHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnHasCascadeDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnFireMoveRightZeroTwoZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnFireMoveRightZeroTwoZeroFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnFireCascadeContent
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnInterleave
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnUnshuffleDenoteStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnShuffleDenoteStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnFireUnshuffleTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnFireUnshuffleTwoFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnHasUnshuffleDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnHasTwoRowSpatialSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihnHasNormalFormCompiler

end FX1PolyAudit
