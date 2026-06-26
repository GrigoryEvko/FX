import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeDrift

/-! # FX1PolyAudit/.../ElimOutputTypeDrift — zero-axiom gate

Per-declaration zero-axiom gate for the per-row eliminator OUTPUT-type drift lemmas (the `outputDrift` the
SR-DSL-5 gate's `elimGateRowReassemble` post-composes): `app` (mixed `subst0` output), the six `subst0 motive
scrutinee` rows, and `idJ` (`idJMotiveAt`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.appOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.boolElimOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.listElimOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.natElimOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.natRecOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.optionMatchOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.eitherMatchOutputTypeDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.idJOutputTypeDriftUnderArgStep

end FX1PolyAudit
