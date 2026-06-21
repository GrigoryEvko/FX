import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.WfContextUnionIrreducibility

/-! # FX1PolyAudit/AuditWfContextUnionIrreducibility — TYTAB-2 WFCTX audit shard

Per-declaration zero-axiom gate for the machine-checked refutation of regularity (the proof that
`WfContextUnion` is an irreducible presupposition, not a derivable theorem): the concrete non-type
`natSuccCellNotUnionType`, the type/term-collapse `regularityImpliesEveryClosedTermIsType`, and the
headline refutation `regularityRefuted`.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.natSuccCellNotUnionType
#assert_no_axioms FX1Poly.Typed.regularityImpliesEveryClosedTermIsType
#assert_no_axioms FX1Poly.Typed.regularityRefuted

end FX1PolyAudit
