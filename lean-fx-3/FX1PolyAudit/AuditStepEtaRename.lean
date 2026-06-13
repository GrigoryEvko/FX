import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaRename

/-! # FX1PolyAudit/AuditStepEtaRename — TABLE-CANON-ETA re-base increment 2

Per-declaration zero-axiom gate for the bespoke-eta rename content
relocated out of `StepRename` (which severs the
`StepRename → StepEta` import edge that made `StepEta` load-bearing for
the canonical typed engine).  These are the eta-source shape
commutations and the `Step.eta` / `etaStar` / `betaEta` / `betaEtaStar`
rename closures.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.rename_etaLamSource
#assert_no_axioms FX1Poly.Core.RawTerm.rename_etaPairSource
#assert_no_axioms FX1Poly.Core.RawTerm.rename_etaPathLamSource
#assert_no_axioms FX1Poly.Core.RawTerm.rename_etaModIntroSource
#assert_no_axioms FX1Poly.Core.RawTerm.rename_etaGlueIntroSource
#assert_no_axioms FX1Poly.Core.Step.eta.rename
#assert_no_axioms FX1Poly.Core.Step.etaStar.rename
#assert_no_axioms FX1Poly.Core.Step.betaEta.rename
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.rename

end FX1PolyAudit
