import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalForm

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfNormalForm —
    zero-axiom gate (the move-past-block cascade denotation)

Per-declaration zero-axiom gate for the discharge of the residual
`ihrMoveRightDenoteResidual`: the nil-cat rewrite helper (`ihnCatNilLeft`); the
move-pair structural predicate (`ihnMovePairSpec`); the cascade denotation
(`ihnMoveRightDenote`) and the residual inhabitant
(`ihnMoveRightDenoteResidualHolds`); the cascade marker (`ihnHasCascadeDenote`);
the kernel span fires with false control and the content fire routing through the
theorem (`ihnFireMoveRightZeroTwoZero`, `ihnFireMoveRightZeroTwoZeroFalse`,
`ihnFireCascadeContent`); the perfect interleave (`ihnInterleave`); the faithful
(un)shuffle denotation statements (`ihnUnshuffleDenoteStatement`,
`ihnShuffleDenoteStatement`, which correct the under-specified
`ihrUnshuffleDenoteResidual`); the (un)shuffle span fires
(`ihnFireUnshuffleTwo`, `ihnFireUnshuffleTwoFalse`).

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

end FX1PolyAudit
