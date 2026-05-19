import LeanFX2.Algo.Progress.Headline.ValueOrCongOnly
import LeanFX2.Algo.Progress.Headline.ArrowApplication
import LeanFX2.Algo.Progress.Headline.SigmaProjections
import LeanFX2.Algo.Progress.Headline.DependentApplication
import LeanFX2.Algo.Progress.Headline.ModalRecordRefine
import LeanFX2.Algo.Progress.Headline.CodataDestSubsume
import LeanFX2.Algo.Progress.Headline.CubicalApplications
import LeanFX2.Algo.Progress.Headline.IdentityEliminators
import LeanFX2.Algo.Progress.Headline.BoolNatEliminators
import LeanFX2.Algo.Progress.Headline.CollectionSumEliminators


namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Unified Wright-Felleisen progress headline (#1565, #1737 close).

Every well-typed `Term` is either in weak head normal form
(`Term.isWHNF someTerm = true`) or takes a `Step` to some
target.  Covers all 77 Term constructors via a single
`cases someTerm` dispatch:

* 61 always-WHNF / cong-only / value-introduction ctors close
  with `Or.inl rfl` — they evaluate to `Term.isWHNF` by
  definition.
* 16 conditional eliminators (`app`, `appPi`, `fst`, `snd`,
  `boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
  `eitherMatch`, `idJ`, `modElim`, `pathApp`, `glueElim`,
  `recordProj`, `refineElim`) route to their focused
  per-construct helper (each shipped earlier in this file).

Zero-axiom under strict policy: every arm is either a
definitional `Or.inl rfl` or an `exact` invocation of a
zero-axiom helper. -/
theorem Term.progress_or_step
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw) :
    Term.isWHNF someTerm = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step someTerm target := by
  cases someTerm with
  | var _ => exact Or.inl rfl
  | unit => exact Or.inl rfl
  | boolTrue => exact Or.inl rfl
  | boolFalse => exact Or.inl rfl
  | natZero => exact Or.inl rfl
  | listNil => exact Or.inl rfl
  | optionNone => exact Or.inl rfl
  | interval0 => exact Or.inl rfl
  | interval1 => exact Or.inl rfl
  | lam _ => exact Or.inl rfl
  | lamPi _ => exact Or.inl rfl
  | pair _ _ => exact Or.inl rfl
  | refl _ _ => exact Or.inl rfl
  | oeqRefl _ _ => exact Or.inl rfl
  | oeqFunext _ _ _ _ _ => exact Or.inl rfl
  | idStrictRefl _ _ _ => exact Or.inl rfl
  | natSucc _ => exact Or.inl rfl
  | listCons _ _ => exact Or.inl rfl
  | optionSome _ => exact Or.inl rfl
  | eitherInl _ => exact Or.inl rfl
  | eitherInr _ => exact Or.inl rfl
  | modIntro _ => exact Or.inl rfl
  | subsume _ => exact Or.inl rfl
  | intervalOpp _ => exact Or.inl rfl
  | intervalMeet _ _ => exact Or.inl rfl
  | intervalJoin _ _ => exact Or.inl rfl
  | pathLam _ _ _ _ _ => exact Or.inl rfl
  | glueIntro _ _ _ _ _ => exact Or.inl rfl
  | transp _ _ _ _ _ _ _ _ _ => exact Or.inl rfl
  | hcomp _ _ _ => exact Or.inl rfl
  | hcompPath _ _ _ _ _ => exact Or.inl rfl
  | recordIntro _ => exact Or.inl rfl
  | refineIntro _ _ _ => exact Or.inl rfl
  | codataUnfold _ _ => exact Or.inl rfl
  | sessionSend _ _ _ => exact Or.inl rfl
  | sessionRecv _ => exact Or.inl rfl
  | effectPerform _ _ _ _ _ _ => exact Or.inl rfl
  | universeCode _ _ _ _ => exact Or.inl rfl
  | cumulUp _ _ _ _ _ _ => exact Or.inl rfl
  | equivReflId _ => exact Or.inl rfl
  | funextRefl _ _ _ => exact Or.inl rfl
  | equivReflIdAtId _ _ _ _ => exact Or.inl rfl
  | funextReflAtId _ _ _ => exact Or.inl rfl
  | equivIntroHet _ _ _ _ => exact Or.inl rfl
  | uaIntroHet _ _ _ _ _ => exact Or.inl rfl
  | funextIntroHet _ _ _ _ => exact Or.inl rfl
  | uaToEquiv _ _ _ _ _ _ _ => exact Or.inl rfl
  | equivApp _ _ => exact Or.inl rfl
  | equivApply _ _ => exact Or.inl rfl
  | arrowCode _ _ _ _ => exact Or.inl rfl
  | piTyCode _ _ _ _ => exact Or.inl rfl
  | sigmaTyCode _ _ _ _ => exact Or.inl rfl
  | productCode _ _ _ _ => exact Or.inl rfl
  | sumCode _ _ _ _ => exact Or.inl rfl
  | listCode _ _ _ => exact Or.inl rfl
  | optionCode _ _ _ => exact Or.inl rfl
  | eitherCode _ _ _ _ => exact Or.inl rfl
  | idCode _ _ _ _ _ => exact Or.inl rfl
  | equivCode _ _ _ _ => exact Or.inl rfl
  | oeqJ _ _ => exact Or.inl rfl
  | idStrictRec _ _ _ => exact Or.inl rfl
  | codataDest _ => exact Or.inl rfl
  | app functionTerm argumentTerm =>
      exact Term.app_progress_or_step functionTerm argumentTerm
  | appPi functionTerm argumentTerm =>
      exact Term.appPi_progress_or_step functionTerm argumentTerm
  | fst pairTerm =>
      exact Term.fst_progress_or_step pairTerm
  | snd pairTerm =>
      exact Term.snd_progress_or_step pairTerm
  | boolElim scrutinee thenBranch elseBranch =>
      exact Term.boolElim_progress_or_step scrutinee thenBranch elseBranch
  | natElim scrutinee zeroBranch succBranch =>
      exact Term.natElim_progress_or_step scrutinee zeroBranch succBranch
  | natRec scrutinee zeroBranch succBranch =>
      exact Term.natRec_progress_or_step scrutinee zeroBranch succBranch
  | listElim scrutinee nilBranch consBranch =>
      exact Term.listElim_progress_or_step scrutinee nilBranch consBranch
  | optionMatch scrutinee noneBranch someBranch =>
      exact Term.optionMatch_progress_or_step scrutinee noneBranch someBranch
  | eitherMatch scrutinee leftBranch rightBranch =>
      exact Term.eitherMatch_progress_or_step scrutinee leftBranch rightBranch
  | idJ baseCase witness =>
      exact Term.idJ_progress_or_step baseCase witness
  | modElim innerTerm =>
      exact Term.modElim_progress_or_step innerTerm
  | pathApp modeIsUnivalent pathTerm intervalTerm =>
      exact Term.pathApp_progress_or_step modeIsUnivalent pathTerm intervalTerm
  | glueElim modeIsUnivalent gluedValue =>
      exact Term.glueElim_progress_or_step modeIsUnivalent gluedValue
  | recordProj recordValue =>
      exact Term.recordProj_progress_or_step recordValue
  | refineElim refinedValue =>
      exact Term.refineElim_progress_or_step refinedValue

end LeanFX2
