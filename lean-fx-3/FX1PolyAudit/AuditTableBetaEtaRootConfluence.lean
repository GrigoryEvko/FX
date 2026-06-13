import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootConfluence
import FX1Poly.Typed.TableBetaEtaRootGuardedConfluence
import FX1Poly.Typed.TableBetaEtaRootCrossQuadrantJoin

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

/-! ## Unique normal forms -/

#assert_no_axioms FX1Poly.Typed.unionStarEqOfNormal
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootUniqueNormalForm

end FX1PolyAudit
