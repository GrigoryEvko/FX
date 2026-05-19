import LeanFX2.Reducibility.Basic

/-! # Tools/Tactics/SN

Strong-normalization proof shorthands.

The reducibility files repeatedly construct `RawTerm.isStronglyNormalizing`
by introducing a `RawStep.parProgress` successor and immediately contradicting
the progress disequality in atomic cases.  These tactics only package that
local choreography.  They do not introduce a new normalization theorem or any
search procedure.
-/

namespace LeanFX2.Tools.Tactics

/-! ## SN constructors -/

syntax "fx_raw_sn_intro " term : tactic
macro_rules
  | `(tactic| fx_raw_sn_intro $sourceTerm) =>
      `(tactic|
        refine LeanFX2.RawTerm.isStronglyNormalizing.intro
          $sourceTerm ?_)

macro "fx_raw_sn_intro_auto" : tactic =>
  `(tactic|
    refine LeanFX2.RawTerm.isStronglyNormalizing.intro _ ?_)

/-! ## Progress contradictions -/

syntax "fx_raw_progress_contra " term " using " term : tactic
macro_rules
  | `(tactic| fx_raw_progress_contra $progressStep using $sourceTargetEq) =>
      `(tactic| exact False.elim ($progressStep.2 $sourceTargetEq))

syntax "fx_raw_progress_refl_contra " term : tactic
macro_rules
  | `(tactic| fx_raw_progress_refl_contra $progressStep) =>
      `(tactic| exact False.elim ($progressStep.2 rfl))

syntax "fx_raw_progress_congr_contra " term " with " term " using " term : tactic
macro_rules
  | `(tactic|
      fx_raw_progress_congr_contra $progressStep with $constructor using $innerEq) =>
      `(tactic|
        exact False.elim
          ($progressStep.2 (congrArg $constructor $innerEq)))

/-! ## Atomic raw SN -/

syntax "fx_raw_atomic_sn_by_inv " term : tactic
macro_rules
  | `(tactic| fx_raw_atomic_sn_by_inv $inversionLemma) =>
      `(tactic|
        exact LeanFX2.RawTerm.isStronglyNormalizing.intro _
          (fun _ progressStep =>
            (progressStep.2 ((($inversionLemma) progressStep.1).symm)).elim))

syntax "fx_raw_atomic_sn_by_inv_symm " term : tactic
macro_rules
  | `(tactic| fx_raw_atomic_sn_by_inv_symm $inversionLemma) =>
      `(tactic|
        exact LeanFX2.RawTerm.isStronglyNormalizing.intro _
          (fun _ progressStep =>
            (progressStep.2 (($inversionLemma) progressStep.1)).elim))

end LeanFX2.Tools.Tactics
