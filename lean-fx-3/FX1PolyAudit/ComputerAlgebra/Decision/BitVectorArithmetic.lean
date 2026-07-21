import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.BitVectorArithmetic

/-! # FX1PolyAudit/ComputerAlgebra/Decision/BitVectorArithmetic — zero-axiom gate
    (bit-level operations as `Z/2^n` arithmetic)

Per-declaration zero-axiom gate for the bit-vector arithmetic bridge: the
hand-rolled Bool kit (`bvaAndElimLeft`/`bvaAndElimRight`/`bvaAndIntro`), the
little-endian value map `bvaToNat` with the fresh doubling power `bvaPow2`
(positivity, `2·v = v + v`), the explicit additive telescopes
(`bvaAddRiffle`/`bvaAddSwapRight`/`bvaMulTwoSwap`, replacing the propext-dirty AC
`simp only` set), the width bound (`bvaConsValueBound`,
`bvaToNatIsBounded`), the full adder (`bvaBitXor`, `bvaFullAdderSum`,
`bvaFullAdderCarry`, the eight-case bit equation), the ripple-carry adder
`bvaAddWithCarryOut` with the carry invariant
(`bvaAddWithCarryOutInvariant` — exact-sum, subtraction-free) and the
truncating `bvaAdd` certified modulo `2^n` (`bvaAddCorrect`), the zero/one
vectors, the cons-only `bvaTake`/`bvaDrop` with the split lemma
(`bvaSplitEquation`) and prefix bound powering the truncating shift
(`bvaShiftLeftTruncToNat` — shifting IS doubling mod `2^n`), the shift-add
multiplier `bvaMulAux`/`bvaMul` certified modulo `2^n` (`bvaMulCorrect`), the
subtraction-free complement identity (`bvaComplementIdentity`) with
two's-complement negation and its cancellation (`bvaNegCancels`), the pointwise
Boolean layer (`bvaZipWith`, xor/and/or, Boolean-ring nilpotence and
idempotence, disjoint-support addition-is-XOR with its exact value corollary),
structural equality (`bvaBitBeq`/`bvaBeq` with reflexivity and soundness),
value injectivity at fixed width (`bvaNatDoubleInjective`, parity via
`bvaEvenDouble`/`bvaOddDouble`, `bvaConsValueSplit`,
`bvaToNatInjectiveOfSameLength`), the ground expression language `BvaExpr`
with evaluation, width well-formedness, eval-length preservation, the decision
`bvaDecideGroundEq` with its sound-and-complete biconditional
(`bvaDecideGroundEqIffToNatEq`), and the DECIDED marker
`fxDissatBv_hasArithmeticBridge = true`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAndElimLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAndElimRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBoolToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaPow2
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaPow2IsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaTwoMulIsAddSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddRiffle
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddSwapRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulTwoSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaConsValueBound
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaToNatIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBitXor
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaFullAdderSum
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaFullAdderCarry
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaFullAdderBitEquation
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddWithCarryOut
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddWithCarryOutLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAdderStepArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddWithCarryOutInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAddCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaZeroes
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaZeroesToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaZeroesLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaOneVector
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaOneVectorLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaOneVectorToNatSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaTake
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDrop
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaTakeLengthOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaSplitStepArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaSplitEquation
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaTakeToNatIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaShiftLeftTrunc
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaShiftLeftTruncLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaShiftLeftTruncToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulAux
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulAuxLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulAuxCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMul
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaMulCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNot
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNotLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBitComplementEquation
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaComplementStepArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaComplementIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNegLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNegCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaZipWith
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaZipWithLength
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaXor
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAnd
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaOr
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaXorSelfIsZeroes
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaAndSelfIsIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaIsAllFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDisjointAddIsXor
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDisjointAddEqXor
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDisjointXorToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBitBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBitBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBitBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaNatDoubleInjective
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaEvenDouble
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaOddDouble
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaConsValueSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaToNatInjectiveOfSameLength
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.constant
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.add
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.mul
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.neg
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.xor
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.and
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.or
#assert_no_axioms FX1Poly.ComputerAlgebra.BvaExpr.not
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaEval
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaExprIsWellFormedAtWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaEvalLengthOfWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDecideGroundEq
#assert_no_axioms FX1Poly.ComputerAlgebra.bvaDecideGroundEqIffToNatEq
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatBv_hasArithmeticBridge

end FX1PolyAudit
