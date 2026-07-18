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
`distributiveLatticeTreeConv_complete` with its two completeness groundings, and the ROUND-2 SOUNDNESS +
DECISION suite: the Boolean DNF evaluation with its comb and characteristic-environment bridges, the clause /
DNF membership and containment kits, the erase-generator kit, the strict clause-order kit (transitivity /
irreflexivity / asymmetry), the three canonicity invariants of `dnfOf` (sorted DNF, sorted clauses,
⊆-antichain) with their full preservation chains, prime-implicant membership recovery, canonical-DNF
uniqueness, `distributiveLatticeTreeConv_sound`, the biconditional
`distributiveLatticeTreeConv_iff_normalForm`, the decider `dlDecideConv` with
`distributiveLatticeTreeConv_iff_decide`, the `Decidable` instance, the two kernel pins, and the decision
marker (the former `fxWalkingDistributiveLattice_minimizationWall` is SUPERSEDED and deleted).  Every landed
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
#assert_no_axioms FX1Poly.Polygraph.dlEvalClause
#assert_no_axioms FX1Poly.Polygraph.dlEvalDnf
#assert_no_axioms FX1Poly.Polygraph.dlEvalMeetOfClause
#assert_no_axioms FX1Poly.Polygraph.dlEvalCombOfDnf
#assert_no_axioms FX1Poly.Polygraph.dlEvalViaDnf
#assert_no_axioms FX1Poly.Polygraph.dlCharacteristicEnv
#assert_no_axioms FX1Poly.Polygraph.dlEvalClauseChar
#assert_no_axioms FX1Poly.Polygraph.dlEvalDnfChar
#assert_no_axioms FX1Poly.Polygraph.dlNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.dlClauseBeq
#assert_no_axioms FX1Poly.Polygraph.dlClauseBeqConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlClauseBeqConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlClauseBeqRefl
#assert_no_axioms FX1Poly.Polygraph.dlClauseBeqEq
#assert_no_axioms FX1Poly.Polygraph.dlDnfHasClause
#assert_no_axioms FX1Poly.Polygraph.dlDnfHasClauseConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlDnfHasClauseConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlDnfHasClauseHead
#assert_no_axioms FX1Poly.Polygraph.dlDnfHasClauseConsWeaken
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberHead
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberConsWeaken
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetIntro
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetElim
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetRefl
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetTrans
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetFalseWitness
#assert_no_axioms FX1Poly.Polygraph.dlEraseGenerator
#assert_no_axioms FX1Poly.Polygraph.dlEraseGeneratorConsDrop
#assert_no_axioms FX1Poly.Polygraph.dlEraseGeneratorConsKeep
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberEraseSelf
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberEraseOther
#assert_no_axioms FX1Poly.Polygraph.dlGenMemberEraseElim
#assert_no_axioms FX1Poly.Polygraph.dlEraseSubset
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetEraseIntro
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessGtFalse
#assert_no_axioms FX1Poly.Polygraph.dlNatLtTrans
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexIrrefl
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessIrrefl
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexAsymm
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessAsymm
#assert_no_axioms FX1Poly.Polygraph.dlClauseLexTrans
#assert_no_axioms FX1Poly.Polygraph.dlClauseLessTrans
#assert_no_axioms FX1Poly.Polygraph.dlIsGenBelowClause
#assert_no_axioms FX1Poly.Polygraph.dlGenBelowClauseConsLe
#assert_no_axioms FX1Poly.Polygraph.dlGenBelowClauseConsGt
#assert_no_axioms FX1Poly.Polygraph.dlGenBelowClauseConsIntro
#assert_no_axioms FX1Poly.Polygraph.dlGenBelowClauseTrans
#assert_no_axioms FX1Poly.Polygraph.dlGenBelowClauseInsert
#assert_no_axioms FX1Poly.Polygraph.dlIsSortedClause
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseConsIntro
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseConsElim
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseInsert
#assert_no_axioms FX1Poly.Polygraph.dlSortedClauseInsertMany
#assert_no_axioms FX1Poly.Polygraph.dlSortedHeadBelow
#assert_no_axioms FX1Poly.Polygraph.dlClauseSubsetAntisymm
#assert_no_axioms FX1Poly.Polygraph.dlIsBelowAllClauses
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllConsIntro
#assert_no_axioms FX1Poly.Polygraph.dlIsSortedDnf
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfConsIntro
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfConsElim
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllMember
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllTrans
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllRemoveSupersets
#assert_no_axioms FX1Poly.Polygraph.dlSortedRemoveSupersets
#assert_no_axioms FX1Poly.Polygraph.dlBelowAllInsertSorted
#assert_no_axioms FX1Poly.Polygraph.dlSortedInsertClauseSorted
#assert_no_axioms FX1Poly.Polygraph.dlSortedInsertClause
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfUnion
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfMeetClause
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfMeet
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfOf
#assert_no_axioms FX1Poly.Polygraph.dlAreClausesSorted
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedConsIntro
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedConsElim
#assert_no_axioms FX1Poly.Polygraph.dlAreClausesSortedMember
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedRemoveSupersets
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedInsertClauseSorted
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedInsertClause
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedDnfUnion
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedDnfMeetClause
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedDnfMeet
#assert_no_axioms FX1Poly.Polygraph.dlClausesSortedDnfOf
#assert_no_axioms FX1Poly.Polygraph.dlDnfIsAntichain
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetOfIntro
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetOfExists
#assert_no_axioms FX1Poly.Polygraph.dlHasSubsetOfFalseMember
#assert_no_axioms FX1Poly.Polygraph.dlMemRemoveSupersets
#assert_no_axioms FX1Poly.Polygraph.dlMemInsertClauseSorted
#assert_no_axioms FX1Poly.Polygraph.dlMemInsertClause
#assert_no_axioms FX1Poly.Polygraph.dlNilDnfIsAntichain
#assert_no_axioms FX1Poly.Polygraph.dlSingletonDnfIsAntichain
#assert_no_axioms FX1Poly.Polygraph.dlInsertClauseAntichain
#assert_no_axioms FX1Poly.Polygraph.dlDnfUnionAntichain
#assert_no_axioms FX1Poly.Polygraph.dlDnfMeetClauseAntichain
#assert_no_axioms FX1Poly.Polygraph.dlDnfMeetAntichain
#assert_no_axioms FX1Poly.Polygraph.dlDnfOfAntichain
#assert_no_axioms FX1Poly.Polygraph.dlCanonicalMemberTransfers
#assert_no_axioms FX1Poly.Polygraph.dlSortedDnfMembersEq
#assert_no_axioms FX1Poly.Polygraph.dlCanonicalDnfUnique
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.dlDnfBeq
#assert_no_axioms FX1Poly.Polygraph.dlDnfBeqConsTrue
#assert_no_axioms FX1Poly.Polygraph.dlDnfBeqConsFalse
#assert_no_axioms FX1Poly.Polygraph.dlDnfBeqRefl
#assert_no_axioms FX1Poly.Polygraph.dlDnfBeqEq
#assert_no_axioms FX1Poly.Polygraph.dlDecideConv
#assert_no_axioms FX1Poly.Polygraph.distributiveLatticeTreeConv_iff_decide
#assert_no_axioms FX1Poly.Polygraph.dlDecidableConv
#assert_no_axioms FX1Poly.Polygraph.dlDecideConv_absorbsPin
#assert_no_axioms FX1Poly.Polygraph.dlDecideConv_separatesMeetJoinPin
#assert_no_axioms FX1Poly.Polygraph.fxWalkingDistributiveLattice_hasNormalFormDecision

end FX1PolyAudit
