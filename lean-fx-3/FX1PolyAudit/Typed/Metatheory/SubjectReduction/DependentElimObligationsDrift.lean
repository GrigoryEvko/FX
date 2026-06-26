import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentElimObligationsDrift

/-! # FX1PolyAudit/.../DependentElimObligationsDrift — zero-axiom gate

Per-declaration zero-axiom gate for the dependent context-fixed eliminator `ObligationsDrift` constructions
(`optionMatch` / `eitherMatch` / `boolElim`).  These are the structurally richest rows the context-fixed driver
(`premisesHoldUnderObligationsDrift`) handles directly: a motive step drifts the branch classifiers (via the
`_stepStable` lemmas for option / either, via `StepStar.subst0Body` for bool) while every obligation context stays
fixed (the motive obligation sits at `context.cons <scrutineeType>` with a motive-independent scrutinee type).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.optionMatchObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.eitherMatchObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.boolElimObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.listElimObligationsDriftUnderArgStep
#assert_no_axioms FX1Poly.Typed.idJObligationsDriftUnderArgStep

end FX1PolyAudit
