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

/-! # Smoke/AuditCoverageGap — explicit #print coverage-gap gates

Reviewer-facing `#print axioms` coverage for load-bearing declarations
that were identified as under-audited.  The build-failing counterpart
lives in `LeanFX2.Tools.AuditAll`.
-/

namespace LeanFX2.Smoke.AuditCoverageGap

-- Term core
#print axioms LeanFX2.Term.subst
#print axioms LeanFX2.Term.rename
#print axioms LeanFX2.Term.toRaw_rename
#print axioms LeanFX2.Term.toRaw_subst
#print axioms LeanFX2.Term.toRaw_weaken
#print axioms LeanFX2.Term.toRaw_subst0

-- Confluence core
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.glueElim_inv
#print axioms LeanFX2.RawStep.par.pathLam_inv

-- D2.5 raw cubical beta rules
#print axioms LeanFX2.RawStep.par.betaPathApp
#print axioms LeanFX2.RawStep.par.betaPathAppDeep
#print axioms LeanFX2.RawStep.par.betaGlueElimIntro
#print axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep

-- Conv core
#print axioms LeanFX2.Conv.refl
#print axioms LeanFX2.Conv.fromStep
#print axioms LeanFX2.Conv.toRawJoin
#print axioms LeanFX2.Conv.canonicalRaw
#print axioms LeanFX2.Conv.transRaw

-- Graded core
#print axioms LeanFX2.Graded.IsLamCompatible
#print axioms LeanFX2.Graded.IsLamCompatibleWithAvailable
#print axioms LeanFX2.Graded.GradeAttribution.scaleBy

-- Dimensions21 registry and aggregate carrier operations
#print axioms LeanFX2.Graded.allDimensionSlots_length
#print axioms LeanFX2.Graded.semiringDimensions21_length
#print axioms LeanFX2.Graded.joinDimensions21_length
#print axioms LeanFX2.Graded.FXGradeVector21.bottom
#print axioms LeanFX2.Graded.FXGradeVector21.le_refl
#print axioms LeanFX2.Graded.FXGradeVector21.le_trans
#print axioms LeanFX2.Graded.FXGradeVector21.joinGrades_bottom_le

end LeanFX2.Smoke.AuditCoverageGap
