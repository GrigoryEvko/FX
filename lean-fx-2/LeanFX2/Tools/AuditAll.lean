import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.Bridge
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.ParRed
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.ConvBridge
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Reduction.Conv
import LeanFX2.Graded.Rules
import LeanFX2.Graded.AtkeyAttack
import LeanFX2.Graded.Dimensions21

/-! # Tools/AuditAll — build-failing zero-axiom gate

This file is intentionally executable: importing it runs
`#assert_no_axioms` over load-bearing kernel declarations.  Unlike
`#print axioms`, these gates fail elaboration when any dependency tree
contains an axiom, including Lean core axioms such as `propext`,
`Quot.sound`, or `Classical.choice`.

This is not yet a generated whole-namespace audit.  It is the first
machine-enforced gate for the current coverage-gap list and the typed
D2.5 path-application parity slice.
-/

namespace LeanFX2.Tools

-- Term core
#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
#assert_no_axioms LeanFX2.Term.toRaw_rename
#assert_no_axioms LeanFX2.Term.toRaw_subst
#assert_no_axioms LeanFX2.Term.toRaw_weaken
#assert_no_axioms LeanFX2.Term.toRaw_subst0

-- Confluence core
#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.par.glueElim_inv
#assert_no_axioms LeanFX2.RawStep.par.pathLam_inv

-- Raw D2.5 cubical beta rules
#assert_no_axioms LeanFX2.RawStep.par.betaPathApp
#assert_no_axioms LeanFX2.RawStep.par.betaPathAppDeep
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep

-- Typed D2.5 path-application parity
#assert_no_axioms LeanFX2.Term.toRaw_interval0
#assert_no_axioms LeanFX2.Term.toRaw_interval1
#assert_no_axioms LeanFX2.Term.toRaw_pathLam
#assert_no_axioms LeanFX2.Term.toRaw_pathApp
#assert_no_axioms LeanFX2.Step.par.pathLam
#assert_no_axioms LeanFX2.Step.par.pathApp
#assert_no_axioms LeanFX2.Step.par.betaPathApp
#assert_no_axioms LeanFX2.Step.par.betaPathAppDeep
#assert_no_axioms LeanFX2.Step.par.toRawBridge

-- Conv core
#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.toRawJoin
#assert_no_axioms LeanFX2.Conv.canonicalRaw
#assert_no_axioms LeanFX2.Conv.transRaw

-- Graded core
#assert_no_axioms LeanFX2.Graded.IsLamCompatible
#assert_no_axioms LeanFX2.Graded.IsLamCompatibleWithAvailable
#assert_no_axioms LeanFX2.Graded.GradeAttribution.scaleBy

-- Dimensions21 registry and aggregate carrier operations
#assert_no_axioms LeanFX2.Graded.allDimensionSlots_length
#assert_no_axioms LeanFX2.Graded.semiringDimensions21_length
#assert_no_axioms LeanFX2.Graded.joinDimensions21_length
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.bottom
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_refl
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_trans
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.joinGrades_bottom_le

-- Namespace sweeps currently known to be clean.  These are still
-- scoped, not a whole-project generated audit.
#audit_namespace LeanFX2.Conv
#audit_namespace LeanFX2.Graded

end LeanFX2.Tools
