import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootStrongNormalization

/-! # FX1PolyAudit/AuditTableBetaEtaRootStrongNormalization — ETA-T6
inc-6b shard

Per-declaration zero-axiom gate for the typed union SN: the typed
iota-table accessibility transfer (bespoke open SN simulated onto
`StepTable` through the adequacy and subject reduction) and the ★★
typed SN for the table beta-eta-root union.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableAccOfTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableBetaEtaRootStronglyNormalizing

end FX1PolyAudit
