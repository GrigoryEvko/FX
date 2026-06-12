import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootConfluence

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

end FX1PolyAudit
