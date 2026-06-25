import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathAppInversion

/-! # FX1PolyAudit/AuditHasTypeUnionPathAppInversion — TYTAB-2 SRINV path-app-inversion audit shard

Per-declaration zero-axiom gate for the union path-elimination (pathApp) inversion — the keystone the
unconditional endpoint-β bundle subject reduction consumes.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtPathAppHead

end FX1PolyAudit
