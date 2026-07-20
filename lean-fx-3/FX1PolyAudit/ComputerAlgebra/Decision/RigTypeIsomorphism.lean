import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.RigTypeIsomorphism

/-! # FX1PolyAudit/ComputerAlgebra/Decision/RigTypeIsomorphism — zero-axiom gate
    (WP-TYPEISO: the free-rig type-isomorphism word problem)

Per-declaration zero-axiom gate for the rig type-isomorphism decision: the clean
Nat scalar kit (`natAddMulClean`/`natAddSwapLeft`/`natAddPosLeftIsNonzero`/
`natCondZeroBothArms` — the propext-dirty `Nat.add_mul`/`Nat.mul_assoc` route is
avoided), the Nat-coefficient sorted term list (`NatTerm`/`NatPoly` with structural
equality and its soundness), the three-way canonical merge `natTermInsert` and its
branch lemmas, `natAdd`/`natScaleTerm`/`natMul` with the annihilation identities,
the `NatPolyCanonical` invariant with canonicity preservation, the additive
coefficient scan `natCoeff` with the term-insert / add homomorphisms and the
canonical-list extensionality keystone `natPolyExtensionality`, the additive rig
AC family (`natAddNilRightIsIdentity`/`natAddComm`/`natAddAssoc`), the `RigType`
carrier with `normalize`/`decideRigIso`, the `RigIso` rig-axiom congruence with its
soundness `rigIsoSound`, the decision correctness (`rigIsoImpliesDecide`/
`decideFalseRefutesRigIso`/`equalNormalFormsDecide`), the two walls
(`rtiHasMultiplicativeSoundness`/`rtiHasExponentialTypeIsoCompleteness`), and the
six ground fires. -/

#assert_no_axioms FX1Poly.ComputerAlgebra.natAddMulClean
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddSwapLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddPosLeftIsNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.natCondZeroBothArms
#assert_no_axioms FX1Poly.ComputerAlgebra.NatTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.NatTerm.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.NatTerm.coefficient
#assert_no_axioms FX1Poly.ComputerAlgebra.NatTerm.exponentVector
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.NatPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.natPolyBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.natPolyBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.natPolyBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.natZeroPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.natOnePoly
#assert_no_axioms FX1Poly.ComputerAlgebra.natVariablePoly
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertNilOnZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertNilOnNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertOnZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertOnCollisionMerge
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertOnGreater
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertOnSmaller
#assert_no_axioms FX1Poly.ComputerAlgebra.natAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.natScaleTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.natMul
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulNilLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natScaleTermNil
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.NatPolyCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.NatPolyCanonical.nilIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.NatPolyCanonical.singleIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.NatPolyCanonical.consIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.natCanonicalHeadNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.natCanonicalTail
#assert_no_axioms FX1Poly.ComputerAlgebra.natCanonicalSkip
#assert_no_axioms FX1Poly.ComputerAlgebra.natCanonicalReplaceHeadCoefficient
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertUnderHead
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermInsertKeepsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddKeepsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.natTermCoeffAt
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeffTermInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeffZeroUnderHead
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeffHeadIsCoefficient
#assert_no_axioms FX1Poly.ComputerAlgebra.natCoeffNonzeroImpliesLessThanHead
#assert_no_axioms FX1Poly.ComputerAlgebra.natPolyExtensionality
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddNilRightIsIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.natAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType.baseAtom
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType.zero
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType.one
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType.add
#assert_no_axioms FX1Poly.ComputerAlgebra.RigType.mul
#assert_no_axioms FX1Poly.ComputerAlgebra.normalize
#assert_no_axioms FX1Poly.ComputerAlgebra.decideRigIso
#assert_no_axioms FX1Poly.ComputerAlgebra.natVariablePolyIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.natOnePolyIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.normalizeIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.addCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.addAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.addComm
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.addZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.addZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.mulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RigIso.mulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.rigIsoSound
#assert_no_axioms FX1Poly.ComputerAlgebra.rigIsoImpliesDecide
#assert_no_axioms FX1Poly.ComputerAlgebra.decideFalseRefutesRigIso
#assert_no_axioms FX1Poly.ComputerAlgebra.equalNormalFormsDecide
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiHasMultiplicativeSoundness
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiHasExponentialTypeIsoCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireDistributivity
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireNonIso
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireLeftDistributivity
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireMulZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.rtiFireControlNonIso
