import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.PostCloneLattice

/-! # FX1PolyAudit/ComputerAlgebra/Decision/PostCloneLattice — zero-axiom gate

Per-declaration zero-axiom gate for the named Post-clone lattice: the truth-table carrier
`PclBoolFn`, the structural micro-kit, the five named-clone preservation predicates
(`pclPreservesZero`/`pclPreservesOne`/`pclIsMonotone`/`pclIsSelfDual`/`pclIsAffine`), clone
membership, the seven-element named-clone inclusion order (reflexivity and transitivity), the sound
Schaefer tractability witness, the capability markers (three left `false`: full Post lattice /
higher-domain dichotomy / clone-generation closure), and the ground fires.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.pclPow2
#assert_no_axioms FX1Poly.ComputerAlgebra.pclLastIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNatLt
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNatLtTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclBoolBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclBoolBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.pclBoolBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclBoolXor
#assert_no_axioms FX1Poly.ComputerAlgebra.pclImplies
#assert_no_axioms FX1Poly.ComputerAlgebra.pclLength
#assert_no_axioms FX1Poly.ComputerAlgebra.pclTableRow
#assert_no_axioms FX1Poly.ComputerAlgebra.pclComplement
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMaskWeight
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMaskLe
#assert_no_axioms FX1Poly.ComputerAlgebra.pclConsAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAllMasks
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMaskIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.PclBoolFn
#assert_no_axioms FX1Poly.ComputerAlgebra.PclBoolFn.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.pclTablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMaskValue
#assert_no_axioms FX1Poly.ComputerAlgebra.pclPreservesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.pclPreservesOne
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMonotonePairOk
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMonotoneAgainst
#assert_no_axioms FX1Poly.ComputerAlgebra.pclMonotoneOuter
#assert_no_axioms FX1Poly.ComputerAlgebra.pclIsMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.pclSelfDualRow
#assert_no_axioms FX1Poly.ComputerAlgebra.pclSelfDualAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pclIsSelfDual
#assert_no_axioms FX1Poly.ComputerAlgebra.pclZhegalkinCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAffineCheck
#assert_no_axioms FX1Poly.ComputerAlgebra.pclIsAffine
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneBottom
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneT0
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneT1
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneM
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneD
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneL
#assert_no_axioms FX1Poly.ComputerAlgebra.PclNamedClone.cloneAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneMembership
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneTag
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneOfTag
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneOfTagTag
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLevel
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLe
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeElim
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeOfEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAllInClone
#assert_no_axioms FX1Poly.ComputerAlgebra.pclIsSchaeferTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasNamedCloneMembership
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasFiniteCloneLattice
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasSchaeferTractabilityDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasFullPostLattice
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasHigherDomainDichotomy
#assert_no_axioms FX1Poly.ComputerAlgebra.pclHasCloneGenerationClosure
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndFn
#assert_no_axioms FX1Poly.ComputerAlgebra.pclXorFn
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNegFn
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNandFn
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndTablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndPreservesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndPreservesOne
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndNotAffine
#assert_no_axioms FX1Poly.ComputerAlgebra.pclXorAffine
#assert_no_axioms FX1Poly.ComputerAlgebra.pclXorNotMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNegSelfDual
#assert_no_axioms FX1Poly.ComputerAlgebra.pclNegNotMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndNotSelfDual
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndRespectsWitnessedPair
#assert_no_axioms FX1Poly.ComputerAlgebra.pclAndInCloneM
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeReflT0
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeBottomAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeT0All
#assert_no_axioms FX1Poly.ComputerAlgebra.pclCloneLeT0T1Incomparable
#assert_no_axioms FX1Poly.ComputerAlgebra.pclSchaeferXorTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.pclSchaeferNandNoWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.pclDecidedMarkers
#assert_no_axioms FX1Poly.ComputerAlgebra.pclWallMarkers

end FX1PolyAudit
