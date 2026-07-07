import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionFormerConvKeepingInversion

/-! # FX1PolyAudit/HasTypeUnionFormerConvKeepingInversion — native former code-inverter audit shard
    (TYTAB-2-RETIRE Tier D)

Per-declaration zero-axiom gate for the native `HasTypeUnion` former code-inverters that retire the grown
former inverters: the Conv-dropping Π-code component corollary, the universe-code inversion corollary, and
the genuinely-new Conv-KEEPING Π-code former inversion. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.inversionPiCodeComponentsUnion
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.inversionUniverseCodeUnion
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertPiTyCodeUnion

end FX1PolyAudit
