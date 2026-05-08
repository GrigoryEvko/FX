import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditConfluence — `#assert_no_axioms` checks for the
confluence cascade.  Covers Conv-level corollaries plus the
underlying raw-level Church-Rosser machinery that makes them
work. -/

#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.transChains
#assert_no_axioms LeanFX2.Conv.toRawJoin
#assert_no_axioms LeanFX2.Conv.canonicalRaw
#assert_no_axioms LeanFX2.Conv.transRaw

/-! ### Raw-level confluence machinery (#1508)

The typed Conv corollaries above lift their proofs through these
raw-level theorems via `Step.parStar.toRawBridge`.  Per audit
ac74bd7e, these were missing from the curated audit catalogue —
their soundness was only checked via `#print axioms` in Smoke
files. -/

#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.parStar.confluence

end LeanFX2.Tools
