import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStar

/-! # Tools/Tactics/Chains

Small chain-building tactic shorthands for reflexive-transitive closures.

These macros do not prove new mathematics.  They expand to the existing
`StepStar`, `Step.parStar`, and `RawStep.parStar` constructors and append
lemmas, keeping chain choreography explicit while removing repetitive
constructor spelling from confluence and reduction proofs.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Generic chain shorthands -/

/-- Close a reflexive chain goal when the closure head is inferable. -/
macro "fx_chain_refl" : tactic =>
  `(tactic|
    first
      | exact LeanFX2.StepStar.refl _
      | exact LeanFX2.Step.parStar.refl _
      | exact LeanFX2.RawStep.parStar.refl _)

/-- Close a one-step chain goal from a matching single-step proof. -/
syntax "fx_chain_single " term : tactic
macro_rules
  | `(tactic| fx_chain_single $singleStep) =>
      `(tactic|
        first
          | exact LeanFX2.StepStar.fromStep $singleStep
          | exact LeanFX2.Step.par.toStar $singleStep
          | exact LeanFX2.RawStep.par.toStar $singleStep)

/-- Append two compatible chain proofs. -/
syntax "fx_chain_append " term " then " term : tactic
macro_rules
  | `(tactic| fx_chain_append $firstChain then $secondChain) =>
      `(tactic|
        first
          | exact LeanFX2.StepStar.append $firstChain $secondChain
          | exact LeanFX2.Step.parStar.append $firstChain $secondChain
          | exact LeanFX2.RawStep.parStar.append $firstChain $secondChain)

/-- Append one final single-step proof to an existing chain. -/
syntax "fx_chain_snoc " term " using " term : tactic
macro_rules
  | `(tactic| fx_chain_snoc $chainProof using $singleStep) =>
      `(tactic|
        first
          | exact LeanFX2.StepStar.snoc $chainProof $singleStep
          | exact LeanFX2.Step.parStar.snoc $chainProof $singleStep
          | exact LeanFX2.RawStep.parStar.snoc $chainProof $singleStep)

/-! ## StepStar-specific shorthands -/

macro "fx_stepstar_refl" : tactic =>
  `(tactic| exact LeanFX2.StepStar.refl _)

syntax "fx_stepstar_step " term " then " term : tactic
macro_rules
  | `(tactic| fx_stepstar_step $singleStep then $restChain) =>
      `(tactic| exact LeanFX2.StepStar.step $singleStep $restChain)

syntax "fx_stepstar_from_step " term : tactic
macro_rules
  | `(tactic| fx_stepstar_from_step $singleStep) =>
      `(tactic| exact LeanFX2.StepStar.fromStep $singleStep)

syntax "fx_stepstar_snoc " term " using " term : tactic
macro_rules
  | `(tactic| fx_stepstar_snoc $chainProof using $singleStep) =>
      `(tactic| exact LeanFX2.StepStar.snoc $chainProof $singleStep)

syntax "fx_stepstar_append " term " then " term : tactic
macro_rules
  | `(tactic| fx_stepstar_append $firstChain then $secondChain) =>
      `(tactic| exact LeanFX2.StepStar.append $firstChain $secondChain)

/-! ## typed Step.parStar-specific shorthands -/

macro "fx_parstar_refl" : tactic =>
  `(tactic| exact LeanFX2.Step.parStar.refl _)

syntax "fx_par_to_star " term : tactic
macro_rules
  | `(tactic| fx_par_to_star $parallelStep) =>
      `(tactic| exact LeanFX2.Step.par.toStar $parallelStep)

syntax "fx_parstar_trans " term " then " term : tactic
macro_rules
  | `(tactic| fx_parstar_trans $parallelStep then $restChain) =>
      `(tactic| exact LeanFX2.Step.parStar.trans $parallelStep $restChain)

syntax "fx_parstar_snoc " term " using " term : tactic
macro_rules
  | `(tactic| fx_parstar_snoc $chainProof using $parallelStep) =>
      `(tactic| exact LeanFX2.Step.parStar.snoc $chainProof $parallelStep)

syntax "fx_parstar_append " term " then " term : tactic
macro_rules
  | `(tactic| fx_parstar_append $firstChain then $secondChain) =>
      `(tactic| exact LeanFX2.Step.parStar.append $firstChain $secondChain)

/-! ## raw RawStep.parStar-specific shorthands -/

macro "fx_raw_parstar_refl" : tactic =>
  `(tactic| exact LeanFX2.RawStep.parStar.refl _)

syntax "fx_raw_par_to_star " term : tactic
macro_rules
  | `(tactic| fx_raw_par_to_star $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.toStar $parallelStep)

syntax "fx_raw_parstar_trans " term " then " term : tactic
macro_rules
  | `(tactic| fx_raw_parstar_trans $parallelStep then $restChain) =>
      `(tactic| exact LeanFX2.RawStep.parStar.trans $parallelStep $restChain)

syntax "fx_raw_parstar_snoc " term " using " term : tactic
macro_rules
  | `(tactic| fx_raw_parstar_snoc $chainProof using $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.parStar.snoc $chainProof $parallelStep)

syntax "fx_raw_parstar_append " term " then " term : tactic
macro_rules
  | `(tactic| fx_raw_parstar_append $firstChain then $secondChain) =>
      `(tactic| exact LeanFX2.RawStep.parStar.append $firstChain $secondChain)

end LeanFX2.Tools.Tactics
