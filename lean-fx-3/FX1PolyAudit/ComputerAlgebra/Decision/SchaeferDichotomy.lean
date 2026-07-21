import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.SchaeferDichotomy

/-! # FX1PolyAudit/ComputerAlgebra/Decision/SchaeferDichotomy — zero-axiom gate

Per-declaration zero-axiom gate for the mechanized Boolean Schaefer dichotomy: the six Schaefer
polymorphisms (`schConst0`/`schConst1`/`schAnd`/`schOr`/`schXor3`/`schMajority3`) bundled as
`schSix`, the concrete constraint relations and languages (2-SAT / Horn / affine / not-all-equal /
one-in-three), the joint-preservation classifier `schIsTractable` with its `schTractabilityWitness`
and `schWitnessSound` soundness, the total dichotomy packaging, the DECIDED capability markers, the
two WALL markers (hardness gadget reduction / higher-domain dichotomy, both `false`), and the
ground fires.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.schConst0
#assert_no_axioms FX1Poly.ComputerAlgebra.schConst1
#assert_no_axioms FX1Poly.ComputerAlgebra.schAnd
#assert_no_axioms FX1Poly.ComputerAlgebra.schOr
#assert_no_axioms FX1Poly.ComputerAlgebra.schXor3
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajority3
#assert_no_axioms FX1Poly.ComputerAlgebra.schSix
#assert_no_axioms FX1Poly.ComputerAlgebra.schOrClauseRel
#assert_no_axioms FX1Poly.ComputerAlgebra.schNandClauseRel
#assert_no_axioms FX1Poly.ComputerAlgebra.sch2SatLang
#assert_no_axioms FX1Poly.ComputerAlgebra.schHornRel
#assert_no_axioms FX1Poly.ComputerAlgebra.schHornLang
#assert_no_axioms FX1Poly.ComputerAlgebra.schAffineRel
#assert_no_axioms FX1Poly.ComputerAlgebra.schAffineLang
#assert_no_axioms FX1Poly.ComputerAlgebra.schNaeRel
#assert_no_axioms FX1Poly.ComputerAlgebra.schNaeLang
#assert_no_axioms FX1Poly.ComputerAlgebra.schOneInThreeRel
#assert_no_axioms FX1Poly.ComputerAlgebra.schOneInThreeLang
#assert_no_axioms FX1Poly.ComputerAlgebra.schPreservesLanguage
#assert_no_axioms FX1Poly.ComputerAlgebra.schOptionIsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.schWitnessSearch
#assert_no_axioms FX1Poly.ComputerAlgebra.schTractabilityWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.schIsTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.schWitnessSearchSound
#assert_no_axioms FX1Poly.ComputerAlgebra.schWitnessSound
#assert_no_axioms FX1Poly.ComputerAlgebra.schTractableHasWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.schIsHardByGadget
#assert_no_axioms FX1Poly.ComputerAlgebra.schDichotomyHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.schDichotomyTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasSixPolymorphisms
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasTractabilityClassifier
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasWitnessSoundness
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasDichotomyWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasBooleanTractabilityDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasHardnessGadgetReduction
#assert_no_axioms FX1Poly.ComputerAlgebra.schHasHigherDomainDichotomy
#assert_no_axioms FX1Poly.ComputerAlgebra.schConst0TablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.schConst1TablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.schOrTablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.schXor3TablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajority3TablePow2
#assert_no_axioms FX1Poly.ComputerAlgebra.schXor3Affine
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajority3SelfDual
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajority3NotAffine
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajorityPreservesOrClause
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajorityPreservesNandClause
#assert_no_axioms FX1Poly.ComputerAlgebra.schMajorityPreserves2Sat
#assert_no_axioms FX1Poly.ComputerAlgebra.schAndNotPreservesOrClause
#assert_no_axioms FX1Poly.ComputerAlgebra.schXor3PreservesAffine
#assert_no_axioms FX1Poly.ComputerAlgebra.schAndPreservesHorn
#assert_no_axioms FX1Poly.ComputerAlgebra.schOrNotPreservesHorn
#assert_no_axioms FX1Poly.ComputerAlgebra.sch2SatTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.schAffineTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.schHornTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.schNaeNotTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.schOneInThreeNotTractable
#assert_no_axioms FX1Poly.ComputerAlgebra.sch2SatWitnessMajority
#assert_no_axioms FX1Poly.ComputerAlgebra.schAffineWitnessXor3
#assert_no_axioms FX1Poly.ComputerAlgebra.schNaeWitnessNone
#assert_no_axioms FX1Poly.ComputerAlgebra.schWitnessSoundOn2Sat
#assert_no_axioms FX1Poly.ComputerAlgebra.schDichotomyOn2Sat
#assert_no_axioms FX1Poly.ComputerAlgebra.schDichotomyOnNae
#assert_no_axioms FX1Poly.ComputerAlgebra.schNaeHardByGadget
#assert_no_axioms FX1Poly.ComputerAlgebra.schDecidedMarkers
#assert_no_axioms FX1Poly.ComputerAlgebra.schWallMarkers

end FX1PolyAudit
