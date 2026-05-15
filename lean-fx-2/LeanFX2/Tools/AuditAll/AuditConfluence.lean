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

/-! ### Asymmetric typed Conv.trans variants (#1590 PHASE7-CONV-TRANS Phase 2)

Asymmetric flavors where one side is a `StepStar` chain and the
other is a `Conv` ship at zero axioms because the typed midpoint is
inherited from the input `Conv`'s existential — no confluence call
required.  Strong subject-reduction with term construction is NOT
needed for these subsets. -/

#assert_no_axioms LeanFX2.Conv.trans_chainLeft
#assert_no_axioms LeanFX2.Conv.trans_chainRight
#assert_no_axioms LeanFX2.Conv.trans_step_left
#assert_no_axioms LeanFX2.Conv.trans_step_right
#assert_no_axioms LeanFX2.Conv.trans_fromStepLeft
#assert_no_axioms LeanFX2.Conv.trans_fromStepRight
#assert_no_axioms LeanFX2.Conv.trans_refl_left
#assert_no_axioms LeanFX2.Conv.trans_refl_right

/-! ### Raw-level confluence machinery (#1508)

The typed Conv corollaries above lift their proofs through these
raw-level theorems via `Step.parStar.toRawBridge`.  Per audit
ac74bd7e, these were missing from the curated audit catalogue —
their soundness was only checked via `#print axioms` in Smoke
files. -/

#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.parStar.confluence

/-! ### parStar cong-rule lifter (mapStep pattern, #1646)

`RawStep.parStar.mapStep` is the raw analog of `StepStar.mapStep` —
the foundational cong-rule lifter used to collapse 21 four-line
refl/trans inductions in `RawParStarCong.lean` to one-line `mapStep`
invocations.  Per `feedback_lean_mapStep_pattern.md`, this is a
load-bearing kernel discipline reused everywhere parStar lifts a
single-step cong rule over the reflexive-transitive closure. -/

#assert_no_axioms LeanFX2.RawStep.parStar.mapStep

end LeanFX2.Tools
