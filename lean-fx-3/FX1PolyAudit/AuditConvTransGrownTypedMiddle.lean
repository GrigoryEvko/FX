import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ConvTransGrownTypedMiddle

/-! # FX1PolyAudit/AuditConvTransGrownTypedMiddle — conv-arm SR closer audit shard

Per-declaration zero-axiom gate for the `Conv`-transitivity-through-a-grown-typeable-middle bridge
(`Conv.trans_of_grownTypedMiddle`, the conversion-arm closer of the native single-step subject reduction —
the TYTAB-2-FT consistency residual, #1697).  Composes the unconditional open-term grown SN capstone with the
per-middle Newman bridge, so it is free of the global `HasStrongNormalization` hypothesis and must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.Conv.trans_of_grownTypedMiddle

end FX1PolyAudit
