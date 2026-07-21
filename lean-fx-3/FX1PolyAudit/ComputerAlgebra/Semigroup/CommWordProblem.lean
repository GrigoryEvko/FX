import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # Commutative-semigroup word problem — zero-axiom gate

Per-declaration zero-axiom gate for the commutative-semigroup word-problem kit: the
Boolean/`Nat` micro-kit, the structural order `cswLe` (reflexive, total, antisymmetric,
transitive), decidable list equality, insertion sort with the crux commutation
`cswInsertComm`, the free commutative-monoid congruence `CswCongr` and its decided word
problem `cswFreeWordDecisionCorrect` (sound and complete), the presented congruence
`CswPresCongr` with the free-embedding bridge and the positive checkable-derivation route
`cswCheckDerivationSound`, the capability markers, and the ground fires.

The full two-sided presented decision is walled (`cswHasPresentedCommWordDecision = false`)
at Dickson's lemma / the almost-full product, needing `WellFounded.fix`; the Gröbner engine
carries only a one-sided certificate (`fxDissatGrob_hasNonMembershipDecision = false`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.cswCondTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCondFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.cswBoolAndElim
#assert_no_axioms FX1Poly.ComputerAlgebra.cswNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cswNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.cswLe
#assert_no_axioms FX1Poly.ComputerAlgebra.cswLeRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cswLeTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.cswLeAntisym
#assert_no_axioms FX1Poly.ComputerAlgebra.cswLeTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.cswListNatBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.cswListNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cswListNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsertConsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsertConsFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.cswSort
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsertAll
#assert_no_axioms FX1Poly.ComputerAlgebra.cswSortAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.cswPairReorder
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsertComm
#assert_no_axioms FX1Poly.ComputerAlgebra.CswCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.CswCongr.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.CswCongr.swap
#assert_no_axioms FX1Poly.ComputerAlgebra.CswCongr.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCongrSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCongrCons
#assert_no_axioms FX1Poly.ComputerAlgebra.cswInsertCongrPrepend
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCongrToSort
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCongrToExpEq
#assert_no_axioms FX1Poly.ComputerAlgebra.cswDecideFreeWord
#assert_no_axioms FX1Poly.ComputerAlgebra.cswDecideFreeWordSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cswDecideFreeWordComplete
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFreeWordDecisionCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.CswRelations
#assert_no_axioms FX1Poly.ComputerAlgebra.cswRelMemBool
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr.swap
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr.rel
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.CswPresCongr.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFreeToPres
#assert_no_axioms FX1Poly.ComputerAlgebra.CswStepWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.CswStepWitness.commStep
#assert_no_axioms FX1Poly.ComputerAlgebra.CswStepWitness.relStep
#assert_no_axioms FX1Poly.ComputerAlgebra.cswStepSource
#assert_no_axioms FX1Poly.ComputerAlgebra.cswStepTarget
#assert_no_axioms FX1Poly.ComputerAlgebra.cswStepValid
#assert_no_axioms FX1Poly.ComputerAlgebra.cswStepGenerator
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCheckDerivation
#assert_no_axioms FX1Poly.ComputerAlgebra.cswCheckDerivationSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cswHasFreeCommWordDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.cswHasPresentedCommWordDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireEqualExponents
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireDifferentExponents
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireDistinctSingletons
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFirePresentedDerivationChecks
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFirePresentedCongruent

end FX1PolyAudit
