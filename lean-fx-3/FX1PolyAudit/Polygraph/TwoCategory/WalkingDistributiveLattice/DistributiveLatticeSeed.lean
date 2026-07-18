import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingDistributiveLattice.DistributiveLatticeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingDistributiveLattice.DistributiveLatticeSeed — zero-axiom gate

Per-declaration zero-axiom gate for the walking bounded distributive lattice on an arbitrary alphabet: the
`LatticeTree` carrier and the `Bool`-lattice evaluation `evalLatticeTree` with its two smokes, the
`DistributiveLatticeTreeConv` fourteen-law convertibility, the Boolean-evaluation soundness
`distributiveLatticeTreeConv_eval_sound` (a genuine sound separator deciding non-convertibility), the
distributivity / meet-absorb-join / join-absorb-meet positive groundings, the distinct-generator and
MEET-≠-JOIN negative groundings, the complete minimal-DNF antichain scaffolding (`genMember` / `clauseSubset` /
`clauseLength` / `clauseLexLess` / `clauseLess` / `dnfHasSubsetOf` / `removeSupersets` / `insertClauseSorted` /
`insertClause` / `dnfUnion` / `canonicalizeDnf` / `dnfMeetClause` / `dnfMeet` / `dnfJoin` / `meetOfClause` /
`combOfDnf` / `dnfOf`) with its separation / absorption smokes, the ABSORPTION LEVER and COMB REDUCTION
(`dlGenMemberMeet` / `dlClauseUnionMeet` / `dlSupersetAbsorbedInJoin` / `dlMeetInsertSortedSet` /
`dlMeetMergeClause` / `dlCombInsertClauseSorted` / `dlHasSubsetAbsorbed` / `dlCombJoinRemoveSupersets` /
`dlCombInsertClause` / `dlCombDnfUnion` / `dlCombDnfMeetClause` / `dlCombDnfMeet` / `dlCombDnfJoin` plus their
algebraic and structural-equation helpers), the NORMALIZATION `dlTreeReducesToDnfComb`, the COMPLETENESS
`distributiveLatticeTreeConv_complete` with its two completeness groundings, and the wall marker.  Every landed
declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the
ordering is the imported structural `natBle` (no `Nat.le`/`Nat.ble` lemma), the clause inserts are cons-only,
and no `List.append` (`++`) or `Int` is used anywhere. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.LatticeTree
#assert_no_axioms FX1Poly.Polygraph.evalLatticeTree
#assert_no_axioms FX1Poly.Polygraph.evalLatticeTree_gen
#assert_no_axioms FX1Poly.Polygraph.evalLatticeTree_meet
#assert_no_axioms FX1Poly.Polygraph.DistributiveLatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeTreeConv_eval_sound
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeDistributes
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeAbsorbs
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeJoinMeetAbsorbs
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeRejectsDistinctGenerators
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeSeparatesMeetJoin
#assert_no_axioms FX1Poly.Polygraph.genMember
#assert_no_axioms FX1Poly.Polygraph.clauseSubset
#assert_no_axioms FX1Poly.Polygraph.clauseLength
#assert_no_axioms FX1Poly.Polygraph.clauseLexLess
#assert_no_axioms FX1Poly.Polygraph.clauseLess
#assert_no_axioms FX1Poly.Polygraph.dnfHasSubsetOf
#assert_no_axioms FX1Poly.Polygraph.removeSupersets
#assert_no_axioms FX1Poly.Polygraph.insertClauseSorted
#assert_no_axioms FX1Poly.Polygraph.insertClause
#assert_no_axioms FX1Poly.Polygraph.dnfUnion
#assert_no_axioms FX1Poly.Polygraph.canonicalizeDnf
#assert_no_axioms FX1Poly.Polygraph.dnfMeetClause
#assert_no_axioms FX1Poly.Polygraph.dnfMeet
#assert_no_axioms FX1Poly.Polygraph.dnfJoin
#assert_no_axioms FX1Poly.Polygraph.meetOfClause
#assert_no_axioms FX1Poly.Polygraph.combOfDnf
#assert_no_axioms FX1Poly.Polygraph.dnfOf
#assert_no_axioms FX1Poly.Polygraph.dnfOf_gen
#assert_no_axioms FX1Poly.Polygraph.dnfOf_top
#assert_no_axioms FX1Poly.Polygraph.dnfOf_bot
#assert_no_axioms FX1Poly.Polygraph.dnfOf_meetTwoGenerators
#assert_no_axioms FX1Poly.Polygraph.dnfOf_joinTwoGenerators
#assert_no_axioms FX1Poly.Polygraph.dnfOf_absorbMeetJoin
#assert_no_axioms FX1Poly.Polygraph.canonicalizeDnf_dropsSuperset
#assert_no_axioms FX1Poly.Polygraph.dlMeetTopLeft
#assert_no_axioms FX1Poly.Polygraph.dlJoinBotLeft
#assert_no_axioms FX1Poly.Polygraph.dlMeetSwapFront
#assert_no_axioms FX1Poly.Polygraph.dlJoinSwapFront
#assert_no_axioms FX1Poly.Polygraph.dlMeetIdemFront
#assert_no_axioms FX1Poly.Polygraph.dlJoinIdemFront
#assert_no_axioms FX1Poly.Polygraph.dlMeetJoinRightDistrib
#assert_no_axioms FX1Poly.Polygraph.dlNatBeqEq
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetConsMem
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexGt
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexLt
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexEqStep
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexAntisymm
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessLt
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessEqStep
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessAntisymm
#assert_no_axioms FX1Poly.Polygraph.dlMeetInsertSortedSet
#assert_no_axioms FX1Poly.Polygraph.dlMeetMergeClause
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberMeet
#assert_no_axioms FX1Poly.Polygraph.dlClauseUnionMeet
#assert_no_axioms FX1Poly.Polygraph.dlSupersetAbsorbedInJoin
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlRemoveSupersetsConsDrop
#assert_no_axioms FX1Poly.Polygraph.dlRemoveSupersetsConsKeep
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseSortedLt
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseSortedGt
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseSortedEq
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseAbsorbed
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseFresh
#assert_no_axioms FX1Poly.Polygraph.dlCombInsertClauseSorted
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetAbsorbed
#assert_no_axioms FX1Poly.Polygraph.dlCombJoinRemoveSupersets
#assert_no_axioms FX1Poly.Polygraph.dlCombInsertClause
#assert_no_axioms FX1Poly.Polygraph.dlCombDnfUnion
#assert_no_axioms FX1Poly.Polygraph.dlCombDnfMeetClause
#assert_no_axioms FX1Poly.Polygraph.dlCombDnfMeet
#assert_no_axioms FX1Poly.Polygraph.dlCombDnfJoin
#assert_no_axioms FX1Poly.Polygraph.dlTreeReducesToDnfComb
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeCommViaCompleteness
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeReductionRoundtrips
#assert_no_axioms FX1Poly.Polygraph.fxWalkingDistributiveLattice_minimizationWall

end FX1PolyAudit
