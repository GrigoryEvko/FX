import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootConfluence
import FX1Poly.Typed.TableBetaEtaRootGuardedConfluence
import FX1Poly.Typed.TableBetaEtaRootCrossQuadrantJoin
import FX1Poly.Typed.TableBetaEtaRootChildJoinPathLam
import FX1Poly.Typed.TableBetaEtaRootChildJoinPair
import FX1Poly.Typed.TableBetaEtaRootChildJoinLam

/-! # FX1PolyAudit/AuditTableBetaEtaRootConfluence — ETA-T6 inc-7
shard

Per-declaration zero-axiom gate for the table-generic typed beta-eta
Church-Rosser: the chain snoc, the typed bespoke-eta-to-table-root
bridge (modal/Glue refuted by untypability), the two star transfers,
and the ★★★ Geuvers theorem over table rows.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.snoc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.bespokeEtaToTableRoot
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.unionStarToBetaEtaStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaEtaStarToUnionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootConfluenceTyped

/-! ## Native guarded-Newman route (no bespoke `Step.eta` round-trip)

The table beta-eta Church-Rosser assembled directly via `newmanGuarded` at the "typed in
context" guard, conditional on the table guarded local join (the cross-quadrant residual). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromLocalJoin

/-! ## Cross-quadrant decomposition (Q1 iota/iota + Q2 eta/eta discharged natively)

The four-quadrant guarded local join reduced to the cross-quadrant (iota/eta) residual alone:
the iota/iota quadrant via `StepTable.confluent`, the eta/eta quadrant via
`StepEtaRootOverTable.deterministic`. -/

#assert_no_axioms FX1Poly.Typed.reflTransClosureStepTableToUnion
#assert_no_axioms FX1Poly.Typed.joinableStepTableToUnion
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableGuardedLocalJoinOfCrossQuadrant
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromCrossQuadrant
#assert_no_axioms FX1Poly.Typed.crossQuadrantIotaStepIsCong
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.crossQuadrantJoinOfChildJoin

/-! ## Per-child copy-replacement join: the path-lambda eta row

The `childJoin` obligation specialized to `etaPathLamRow` — the clean
(guard-free) cross-quadrant residual case: the path-beta-vs-eta peak
joins by equality at the core; the function-slot congruence joins at the
reflected reduct. -/

#assert_no_axioms FX1Poly.Typed.etaPathLamRow_memTable
#assert_no_axioms FX1Poly.Typed.noStepTableFromVarCell
#assert_no_axioms FX1Poly.Typed.etaPathLamRowContraction_introChildrenShape
#assert_no_axioms FX1Poly.Typed.childJoinPathLam

/-! ## Per-child copy-replacement join: the pair (Sigma-intro) eta row

The `childJoin` obligation specialized to `etaPairRow` — the
MULTI-OBSERVATION (surjective-pairing) cross-quadrant residual case: a
projection iota peak joins at the core after re-aligning the other
projected copy by the dual projection; a core congruence joins at the
reflected reduct after re-aligning by the same core-step. -/

#assert_no_axioms FX1Poly.Typed.etaPairRow_memTable
#assert_no_axioms FX1Poly.Typed.iotaRowAtFstIsFstPair
#assert_no_axioms FX1Poly.Typed.iotaRowAtSndIsSndPair
#assert_no_axioms FX1Poly.Typed.fstPairRowFiringDecompose
#assert_no_axioms FX1Poly.Typed.sndPairRowFiringDecompose
#assert_no_axioms FX1Poly.Typed.etaPairRowContraction_introChildrenShape
#assert_no_axioms FX1Poly.Typed.childJoinPair

/-! ## Per-child copy-replacement join: the function-lambda eta row

The `childJoin` obligation specialized to `etaLamRow` — the
GENUINELY-TYPED (Nederpelt annotation clash) cross-quadrant residual
case, the SOLE childJoin consuming the typed `guardOrigin`: the domain
slot steps disjointly from the observation (joins by the unchanged eta
contraction); the root-beta-vs-eta peak joins through the typed
annotation joinability `etaLamSourceAnnotationJoinable` replayed through
the lambda's domain child; the function-slot congruence joins at the
reflected reduct. -/

#assert_no_axioms FX1Poly.Typed.etaLamRow_memTable
#assert_no_axioms FX1Poly.Typed.betaRowFiringDecompose
#assert_no_axioms FX1Poly.Typed.etaLamRowContraction_introChildrenShape
#assert_no_axioms FX1Poly.Typed.childJoinLam

/-! ## Unique normal forms -/

#assert_no_axioms FX1Poly.Typed.unionStarEqOfNormal
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootUniqueNormalForm

end FX1PolyAudit
