import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.PrimeEventStructure

/-! # FX1PolyAudit/Polygraph/Net/PrimeEventStructure — zero-axiom gate (NET-14)

Per-declaration `#assert_no_axioms` gate over every headline of the prime-event-structure
brick (`FX1Poly.Polygraph.Net`): the Boolean micro-kit, the cons-only list utilities, the
`EventStructure` carrier + constructor, the symmetric conflict lookup, the structural
fuel-bounded causal reachability, well-formedness, configuration validity
(conflict-free + down-closed), the covering / equality machinery, the extend-preserves-
validity keystone and its soundness corollaries, the two infinite-construction walls, the
capability markers, and the ground fires.  Parity is EXACT with the shipped file: one
directive per shipped declaration (the `EventStructure` inductive plus its constructor).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.evsBoth
#assert_no_axioms FX1Poly.Polygraph.Net.evsCondTrue
#assert_no_axioms FX1Poly.Polygraph.Net.evsCondFalse
#assert_no_axioms FX1Poly.Polygraph.Net.evsBothIntro
#assert_no_axioms FX1Poly.Polygraph.Net.evsBothElim
#assert_no_axioms FX1Poly.Polygraph.Net.evsNegate
#assert_no_axioms FX1Poly.Polygraph.Net.evsLength
#assert_no_axioms FX1Poly.Polygraph.Net.evsAppend
#assert_no_axioms FX1Poly.Polygraph.Net.evsMemBool
#assert_no_axioms FX1Poly.Polygraph.Net.evsMemConsSelf
#assert_no_axioms FX1Poly.Polygraph.Net.evsMemConsMono
#assert_no_axioms FX1Poly.Polygraph.Net.EventStructure
#assert_no_axioms FX1Poly.Polygraph.Net.EventStructure.mk
#assert_no_axioms FX1Poly.Polygraph.Net.evsPairMemBool
#assert_no_axioms FX1Poly.Polygraph.Net.evsInConflict
#assert_no_axioms FX1Poly.Polygraph.Net.evsSuccsOf
#assert_no_axioms FX1Poly.Polygraph.Net.evsExpandAll
#assert_no_axioms FX1Poly.Polygraph.Net.evsReachSet
#assert_no_axioms FX1Poly.Polygraph.Net.evsCausesLe
#assert_no_axioms FX1Poly.Polygraph.Net.evsSymmetricFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsIrreflexiveFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsInheritOverEdges
#assert_no_axioms FX1Poly.Polygraph.Net.evsInheritFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Net.evsNoConflictWith
#assert_no_axioms FX1Poly.Polygraph.Net.evsIsConflictFree
#assert_no_axioms FX1Poly.Polygraph.Net.evsDownClosedFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsIsDownClosed
#assert_no_axioms FX1Poly.Polygraph.Net.evsIsConfiguration
#assert_no_axioms FX1Poly.Polygraph.Net.evsPredsInFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsPredecessorsIn
#assert_no_axioms FX1Poly.Polygraph.Net.evsEnabled
#assert_no_axioms FX1Poly.Polygraph.Net.evsConfigEq
#assert_no_axioms FX1Poly.Polygraph.Net.evsExtendsBy
#assert_no_axioms FX1Poly.Polygraph.Net.evsCoversFold
#assert_no_axioms FX1Poly.Polygraph.Net.evsCovers
#assert_no_axioms FX1Poly.Polygraph.Net.evsDownClosedFoldExtend
#assert_no_axioms FX1Poly.Polygraph.Net.evsExtendPreservesConfig
#assert_no_axioms FX1Poly.Polygraph.Net.evsExtendsBySound
#assert_no_axioms FX1Poly.Polygraph.Net.evsConfigEqSound
#assert_no_axioms FX1Poly.Polygraph.Net.evsCoversSound
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasPetriUnfolding
#assert_no_axioms FX1Poly.Polygraph.Net.evsUnfoldingWallEqualsDickson
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasInfiniteDomainCompleteness
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasConfigurationDecision
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasConfigEquality
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasCoveringDecision
#assert_no_axioms FX1Poly.Polygraph.Net.evsHasExtendPreservation
#assert_no_axioms FX1Poly.Polygraph.Net.evsExample
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireConfigValid
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireConflictInvalid
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireDownClosedFails
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireEnabled
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireExtendStaysConfig
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireConfigEqReorder
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireConfigNeq
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireCausesLeTrue
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireCausesLeFalse
#assert_no_axioms FX1Poly.Polygraph.Net.evsFireWellFormed

end FX1PolyAudit
