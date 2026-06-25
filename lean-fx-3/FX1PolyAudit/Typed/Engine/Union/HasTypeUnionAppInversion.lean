import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionAppInversion

/-! # FX1PolyAudit/AuditHasTypeUnionAppInversion — TYTAB-2 SRINV app-inversion audit shard

Per-declaration zero-axiom gate for the union Π-elimination (app) inversion — the keystone the
unconditional β / endpoint-β bundle subject reduction consumes.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtAppHead

end FX1PolyAudit
