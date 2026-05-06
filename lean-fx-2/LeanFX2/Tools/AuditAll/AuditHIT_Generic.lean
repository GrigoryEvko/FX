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

/-! ## AuditHIT_Generic — 32 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.EmptyPathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.hasPathBetween
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete_hasNoPath
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.preservesRelation
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.indiscrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.fromEquivalence
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run_respects
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant_run
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.run
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.run_respects
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.constant
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.constant_run
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.quotientUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.propTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.setTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.s1BaseUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.suspensionNorthUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutLeftUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerPointUnit

end LeanFX2.Tools
