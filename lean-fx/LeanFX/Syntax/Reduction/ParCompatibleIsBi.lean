import LeanFX.Syntax.Reduction.ParCompatible
import LeanFX.Syntax.Reduction.ParBi

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # `Step.par.{rename,subst}_compatible` preserve `Step.par.isBi`.

The isBi siblings of `Step.par.rename_compatible` and
`Step.par.subst_compatible`.  Same case enumeration as the
underlying compat theorems but constructing `Step.par.isBi` of
the result.

These are needed by the witnessed joint-substitution lemma
`Step.par.subst_par_witnessed` (in `ParSubstPointwiseIsBi.lean`),
which in turn drives the β cases of `Step.par.cd_monotone` for
typed Church-Rosser (W8.3 / #885).

Proof strategy: induction on the `isBi` witness.  After matching
the constructor pattern, the underlying par-step's compat function
reduces definitionally to the corresponding constructor case body.
We rebuild the matching `Step.par.isBi.<C>` constructor application,
threading the cast-preservation lemmas (`isBi.castBoth_eq`,
`isBi.cast_target_eq`, `isBi.cast_source_eq`) at every cast site.

η-cases (`etaArrow`, `etaSigma`) are excluded — `Step.par.isBi`
omits them by design.

This file is large but mechanical: each of ~50 cases mirrors the
corresponding case in `ParCompatible.lean` line-for-line. -/

/-- `Step.par.rename_compatible` preserves `Step.par.isBi`. -/
theorem Step.par.rename_compatible_isBi
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.par.isBi
      (Step.par.rename_compatible termRenaming parallelStep) := by
  induction stepBi generalizing targetScope targetCtx with
  | refl term => exact Step.par.isBi.refl _
  | app _funBi _argBi funIH argIH =>
      exact Step.par.isBi.app (funIH termRenaming) (argIH termRenaming)
  | lam _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      exact Step.par.isBi.lam
        (Step.par.isBi.castBoth_eq _
          (bodyIH (TermRenaming.lift termRenaming domainType)))
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      exact Step.par.isBi.lamPi
        (bodyIH (TermRenaming.lift termRenaming domainType))
  | appPi _funBi _argBi funIH argIH =>
      exact Step.par.isBi.castBoth_eq _
        (Step.par.isBi.appPi (funIH termRenaming) (argIH termRenaming))
  | pair _firstBi _secondBi firstIH secondIH =>
      exact Step.par.isBi.pair
        (firstIH termRenaming)
        (Step.par.isBi.castBoth_eq _ (secondIH termRenaming))
  | fst _pairBi pairIH =>
      exact Step.par.isBi.fst (pairIH termRenaming)
  | snd _pairBi pairIH =>
      exact Step.par.isBi.castBoth_eq _
        (Step.par.isBi.snd (pairIH termRenaming))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      exact Step.par.isBi.boolElim
        (scrutIH termRenaming) (thenIH termRenaming) (elseIH termRenaming)
  | natSucc _predBi predIH =>
      exact Step.par.isBi.natSucc (predIH termRenaming)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      exact Step.par.isBi.natElim
        (scrutIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      exact Step.par.isBi.natRec
        (scrutIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | listCons _headBi _tailBi headIH tailIH =>
      exact Step.par.isBi.listCons
        (headIH termRenaming) (tailIH termRenaming)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      exact Step.par.isBi.listElim
        (scrutIH termRenaming) (nilIH termRenaming) (consIH termRenaming)
  | optionSome _valueBi valueIH =>
      exact Step.par.isBi.optionSome (valueIH termRenaming)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      exact Step.par.isBi.optionMatch
        (scrutIH termRenaming) (noneIH termRenaming) (someIH termRenaming)
  | eitherInl _valueBi valueIH =>
      exact Step.par.isBi.eitherInl (valueIH termRenaming)
  | eitherInr _valueBi valueIH =>
      exact Step.par.isBi.eitherInr (valueIH termRenaming)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      exact Step.par.isBi.eitherMatch
        (scrutIH termRenaming) (leftIH termRenaming) (rightIH termRenaming)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      exact Step.par.isBi.idJ
        (baseIH termRenaming) (witnessIH termRenaming)
  -- β shallow cases: target involves a `subst0` post-redex; the
  -- compat function uses HEq plumbing through `castTarget` to
  -- align it with the renamed pre-substitution form.  The isBi
  -- mirror uses `castTarget_eq` to push isBi through the
  -- alignment cast, then rebuilds the inner `betaApp`/etc.
  -- TODO: betaApp / betaAppPi / betaFstPair / betaSndPair (and their Deep
  -- variants) — these β cases have HEq plumbing through `castTarget` /
  -- `castSource` to align renamed `subst0` with renamed pre-β form.  The
  -- cleanest path is to prove a parWithBi-valued `rename_compatible`
  -- companion that constructs both Step.par and Step.par.isBi inline at
  -- each cast site (rather than mirroring as a separate isBi proof).
  -- This work continues across multiple Ralph iterations.
  | _ => sorry

end LeanFX.Syntax
