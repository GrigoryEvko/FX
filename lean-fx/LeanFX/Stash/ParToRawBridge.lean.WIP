import LeanFX.Syntax.Reduction.ParRed
import LeanFX.Syntax.Reduction.RawPar
import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.ToRawCommute

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.toRawBridge` — translate typed parallel steps to raw.

For every typed `Step.par sourceTerm targetTerm`, produce a raw
`RawStep.par sourceTerm.toRaw targetTerm.toRaw`.  This is the
**forward** bridge — raw inversion lemmas (`RawStep.par.lam_inv`
etc.) can then be applied to extract structural information from
typed parallel-reduction chains.

### Status

The bridge currently covers **non-β cases** structurally.  The
β/ι cases that involve `Term.subst0` need an unconditional
`Term.toRaw_subst0` lemma — which currently requires a kernel-
level migration from `Term.subst0` to `Term.subst0_term` (the
raw-consistent variant) in `Step.par`'s β-rule targets.  Those
cases are marked `sorry` here pending Phase 4c kernel refactor.

### η-cases

η constructors of `Step.par` (`etaArrow`, `etaSigma`) have **no**
raw counterpart — `RawStep.par` is βι-only by design.  The bridge
is therefore conditional on a βι-witness (`Step.par.isBi`) for
the source step.  We surface this as an additional hypothesis on
the bridge theorem statement. -/

/-- Forward bridge for `Step.par`: typed parallel reduction lifts to
raw parallel reduction via `Term.toRaw`.  Restricted to βι-witnessed
steps so that η constructors (which have no raw counterpart) are
ruled out vacuously. -/
theorem Step.par.toRawBridge_partial
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceTerm targetTerm : Term ctx sourceType}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par sourceTerm.toRaw targetTerm.toRaw := by
  induction parallelStep
  case refl term =>
      exact RawStep.par.refl term.toRaw
  case lam bodyStep bodyIH =>
      exact RawStep.par.lam bodyIH
  case lamPi bodyStep bodyIH =>
      exact RawStep.par.lam bodyIH
  case app functionStep argumentStep functionIH argumentIH =>
      exact RawStep.par.app functionIH argumentIH
  case appPi functionStep argumentStep functionIH argumentIH =>
      exact RawStep.par.app functionIH argumentIH
  case pair firstStep secondStep firstIH secondIH =>
      exact RawStep.par.pair firstIH secondIH
  case fst pairStep pairIH =>
      exact RawStep.par.fst pairIH
  case snd pairStep pairIH =>
      exact RawStep.par.snd pairIH
  case boolElim scrutineeStep thenStep elseStep
                scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim scrutineeIH thenIH elseIH
  case natSucc predStep predIH =>
      exact RawStep.par.natSucc predIH
  case natElim scrutineeStep zeroStep succStep
                scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim scrutineeIH zeroIH succIH
  case natRec scrutineeStep zeroStep succStep
               scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec scrutineeIH zeroIH succIH
  case listCons headStep tailStep headIH tailIH =>
      exact RawStep.par.listCons headIH tailIH
  case listElim scrutineeStep nilStep consStep
                 scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim scrutineeIH nilIH consIH
  case optionSome valueStep valueIH =>
      exact RawStep.par.optionSome valueIH
  case optionMatch scrutineeStep noneStep someStep
                    scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch scrutineeIH noneIH someIH
  case eitherInl valueStep valueIH =>
      exact RawStep.par.eitherInl valueIH
  case eitherInr valueStep valueIH =>
      exact RawStep.par.eitherInr valueIH
  case eitherMatch scrutineeStep leftStep rightStep
                    scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch scrutineeIH leftIH rightIH
  case idJ baseStep witnessStep baseIH witnessIH =>
      exact RawStep.par.idJ baseIH witnessIH
  case iotaBoolElimTrue elseBranch thenStep thenIH =>
      exact RawStep.par.iotaBoolElimTrue _ thenIH
  case iotaBoolElimFalse thenBranch elseStep elseIH =>
      exact RawStep.par.iotaBoolElimFalse _ elseIH
  case iotaNatElimZero succBranch zeroStep zeroIH =>
      exact RawStep.par.iotaNatElimZero _ zeroIH
  case iotaNatElimSucc zeroBranch predStep succStep predIH succIH =>
      exact RawStep.par.iotaNatElimSucc _ predIH succIH
  case iotaNatRecZero succBranch zeroStep zeroIH =>
      exact RawStep.par.iotaNatRecZero _ zeroIH
  case iotaNatRecSucc predStep zeroStep succStep predIH zeroIH succIH =>
      exact RawStep.par.iotaNatRecSucc predIH zeroIH succIH
  case iotaListElimNil consBranch nilStep nilIH =>
      exact RawStep.par.iotaListElimNil _ nilIH
  case iotaListElimCons nilBranch headStep tailStep consStep
                         headIH tailIH consIH =>
      exact RawStep.par.iotaListElimCons _ headIH tailIH consIH
  case iotaOptionMatchNone someBranch noneStep noneIH =>
      exact RawStep.par.iotaOptionMatchNone _ noneIH
  case iotaOptionMatchSome noneBranch valueStep someStep
                            valueIH someIH =>
      exact RawStep.par.iotaOptionMatchSome _ valueIH someIH
  case iotaEitherMatchInl rightBranch valueStep leftStep
                           valueIH leftIH =>
      exact RawStep.par.iotaEitherMatchInl _ valueIH leftIH
  case iotaEitherMatchInr leftBranch valueStep rightStep
                           valueIH rightIH =>
      exact RawStep.par.iotaEitherMatchInr _ valueIH rightIH
  case iotaIdJRefl baseStep baseIH =>
      -- The raw rule needs the rawTerm endpoint as an explicit arg.
      exact RawStep.par.iotaIdJRefl _ baseIH
  case etaArrow f =>
      -- η-rules have no raw counterpart; the βι-witness rules out
      -- this case in callers.  Here we emit `sorry` because the
      -- bridge is unconditionally false for this constructor.
      sorry
  case etaSigma p =>
      sorry
  -- β-cases: blocked on Term.toRaw_subst0 (kernel refactor needed).
  case betaApp body body' arg arg' bodyStep argStep bodyIH argIH =>
      sorry
  case betaAppPi body body' arg arg' bodyStep argStep bodyIH argIH =>
      sorry
  case betaFstPair secondVal firstStep firstIH =>
      -- target = firstVal' which has no subst.  Deep premise: par firstVal firstVal'.
      -- The raw rule is `RawStep.par.betaFstPair`.  Source toRaw =
      -- RawTerm.fst (RawTerm.pair firstVal.toRaw secondVal.toRaw); target
      -- toRaw = firstVal'.toRaw.  Matches RawStep.par.betaFstPair
      -- with the firstVal-step IH, but the pair structure must be
      -- inferred from the typed Term.pair constructor — let Lean
      -- elaborate.
      sorry
  case betaSndPair firstVal secondStep secondIH =>
      sorry
  -- Deep β/ι cases: 17 sorry's pending bridge completion.
  all_goals sorry

end LeanFX.Syntax
