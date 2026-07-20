import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # FX1PolyAudit/ComputerAlgebra/Semigroup/CommWordProblem — zero-axiom gate
    (NET-3 brick: the commutative-semigroup word problem)

Per-declaration zero-axiom gate for the commutative-semigroup word-problem kit: the
Boolean/`Nat` micro-kit, the structural order `cswLe` (refl / total / antisym / trans),
decidable list equality, insertion sort with the crux commutation `cswInsertComm`, the
free commutative-monoid congruence `CswCongr` and its DECIDED word problem
(`cswFreeWordDecisionCorrect` — sound and complete), the presented congruence
`CswPresCongr` with the free-embedding bridge and the POSITIVE checkable-derivation route
(`cswCheckDerivationSound`), the capability markers, and the ground fires.

The FULL two-sided presented decision is WALLED (`cswHasPresentedCommWordDecision = false`):
deciding non-congruence needs a confluent terminating completion whose termination is
Dickson's lemma / the almost-full product — a certified zero-axiom impossibility here
(`fxNet4_dicksonWall`, needs `WellFounded.fix`); the shipped Gröbner engine carries only a
one-sided certificate (`fxDissatGrob_hasNonMembershipDecision = false`).

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
#assert_no_axioms FX1Poly.ComputerAlgebra.cswHasPresentedPositiveCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.cswHasPresentedCommWordDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireEqualExponents
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireDifferentExponents
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFireDistinctSingletons
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFirePresentedDerivationChecks
#assert_no_axioms FX1Poly.ComputerAlgebra.cswFirePresentedCongruent

end FX1PolyAudit
