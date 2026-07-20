import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.TwoGroup.SemidirectWordProblem

/-! # FX1PolyAudit.Polygraph.TwoCategory.TwoGroup.SemidirectWordProblem — zero-axiom gate (the
crossed-module / free-2-group word problem for `G ⋉ C` at the abelian / trivial-action fragment)

Per-declaration zero-axiom gate: the structural `Bool` equalities for the base (`cxmSignedListBeq`) and
fibre (`cxmNatListBeq`) coordinates with their reflexivity/soundness, the cons-only fibre append and
insertion-sort normal form, the `CrossedCell` carrier + identity + trivial action + semidirect
`cxmCompose` + well-formedness, the `decideTwoGroupEq` decision with its characterisation, the
`TwoGroupConv` congruence with soundness and abelian-fragment completeness and the decision
biconditional, the equivariance / Peiffer `Bool` checks with their concrete instance-holds /
non-instance-refuted witnesses, the five groundings, the two walls, and the marker.  All free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `funext`, `omega`, `Int`, `Nat.sub`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cxmBoolBeq
#assert_no_axioms FX1Poly.Polygraph.cxmBoolBeqRefl
#assert_no_axioms FX1Poly.Polygraph.cxmBoolBeqSound
#assert_no_axioms FX1Poly.Polygraph.cxmSignedGenBeq
#assert_no_axioms FX1Poly.Polygraph.cxmSignedGenBeqRefl
#assert_no_axioms FX1Poly.Polygraph.cxmSignedGenBeqSound
#assert_no_axioms FX1Poly.Polygraph.cxmSignedListBeq
#assert_no_axioms FX1Poly.Polygraph.cxmSignedListBeqRefl
#assert_no_axioms FX1Poly.Polygraph.cxmSignedListBeqSound
#assert_no_axioms FX1Poly.Polygraph.cxmNatListBeq
#assert_no_axioms FX1Poly.Polygraph.cxmNatListBeqRefl
#assert_no_axioms FX1Poly.Polygraph.cxmNatListBeqSound
#assert_no_axioms FX1Poly.Polygraph.cxmNatAppend
#assert_no_axioms FX1Poly.Polygraph.cxmInsert
#assert_no_axioms FX1Poly.Polygraph.cxmSort
#assert_no_axioms FX1Poly.Polygraph.CrossedCell
#assert_no_axioms FX1Poly.Polygraph.cxmIdentityCell
#assert_no_axioms FX1Poly.Polygraph.cxmActionTrivial
#assert_no_axioms FX1Poly.Polygraph.cxmCompose
#assert_no_axioms FX1Poly.Polygraph.cxmWellFormed
#assert_no_axioms FX1Poly.Polygraph.cxmIdentityWellFormed
#assert_no_axioms FX1Poly.Polygraph.decideTwoGroupEq
#assert_no_axioms FX1Poly.Polygraph.decideTwoGroupEq_true_iff
#assert_no_axioms FX1Poly.Polygraph.TwoGroupConv
#assert_no_axioms FX1Poly.Polygraph.twoGroupConv_normalForms
#assert_no_axioms FX1Poly.Polygraph.twoGroupConv_sound
#assert_no_axioms FX1Poly.Polygraph.twoGroupConv_complete
#assert_no_axioms FX1Poly.Polygraph.decideTwoGroupEq_iff_conv
#assert_no_axioms FX1Poly.Polygraph.conjugateBase
#assert_no_axioms FX1Poly.Polygraph.cxmBoundaryTrivial
#assert_no_axioms FX1Poly.Polygraph.cxmBoundaryColour
#assert_no_axioms FX1Poly.Polygraph.cxmActionDouble
#assert_no_axioms FX1Poly.Polygraph.cxmEquivarianceHolds
#assert_no_axioms FX1Poly.Polygraph.cxmPeifferHolds
#assert_no_axioms FX1Poly.Polygraph.cxmEquivarianceHoldsOnTrivialInstance
#assert_no_axioms FX1Poly.Polygraph.cxmEquivarianceRefutedOnColourWitness
#assert_no_axioms FX1Poly.Polygraph.cxmPeifferHoldsOnTrivialInstance
#assert_no_axioms FX1Poly.Polygraph.cxmPeifferRefutedOnDoublingWitness
#assert_no_axioms FX1Poly.Polygraph.cxmIdentityLeftUnitFires
#assert_no_axioms FX1Poly.Polygraph.cxmFibreReorderDecidesEqual
#assert_no_axioms FX1Poly.Polygraph.cxmFibreReorderConv
#assert_no_axioms FX1Poly.Polygraph.cxmDistinctBaseDecidesUnequal
#assert_no_axioms FX1Poly.Polygraph.cxmDistinctFibreDecidesUnequal
#assert_no_axioms FX1Poly.Polygraph.cxmHasNonAbelianPeiffer
#assert_no_axioms FX1Poly.Polygraph.cxmHasIdentitiesAmongRelations
#assert_no_axioms FX1Poly.Polygraph.cxmHasSemidirectAbelianWordDecision

end FX1PolyAudit
