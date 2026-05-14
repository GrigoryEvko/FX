import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step
import LeanFX2.Algo.Progress.CanonicalIntroductions
import LeanFX2.Algo.Progress.CanonicalTypeCodes
import LeanFX2.Algo.Progress.CanonicalInterval
import LeanFX2.Algo.Progress.CanonicalHoTTRefl
import LeanFX2.Algo.Progress.BetaIotaStepProvability
import LeanFX2.Algo.Progress.CongRuleLifters

/-! # LeanFX2.Algo.Progress.Headline.ValueOrCongOnly

Always-WHNF half of Wright-Felleisen Progress: every term whose
head ctor is a value-introduction (57 always-WHNF heads) or one
of the three cong-only eliminators (`oeqJ`, `idStrictRec`,
`codataDest`) is in WHNF directly.

Carved out of the monolithic `LeanFX2/Algo/Progress/Headline.lean`
for compile-time parallelism (per-Term-head sub-modules).
Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Always-WHNF half of progress: every value-introduction Term
ctor is in WHNF.  This covers the 57 always-WHNF heads
(canonical leaf values, value introductions, type codes, HoTT
canonical refl-fragment witnesses) plus the 3 cong-only
eliminators (`oeqJ`, `idStrictRec`, `codataDest`).

The theorem statement uses an `Or` disjunction matching the
shape of the future full `Term.progress_or_step` headline; the
`Or.inr` case is impossible for these heads (no β/ι rule fires
from a value form), so the proof always picks `Or.inl rfl`.

For conditional eliminator heads (`app`, `appPi`, `fst`, `snd`,
`boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
`eitherMatch`, `idJ`, `modElim`, `pathApp`, `glueElim`,
`recordProj`, `refineElim`, `subsume`), see the per-construct
helpers (`Term.app_progress_or_step` is shipped here; others
are deferred — see the docstring of the M05.D section above). -/
theorem Term.value_or_cong_only_progress
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (notConditionalElim :
      someTerm.headCtor ≠ Term.HeadCtor.app ∧
      someTerm.headCtor ≠ Term.HeadCtor.appPi ∧
      someTerm.headCtor ≠ Term.HeadCtor.fst ∧
      someTerm.headCtor ≠ Term.HeadCtor.snd ∧
      someTerm.headCtor ≠ Term.HeadCtor.boolElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.natElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.natRec ∧
      someTerm.headCtor ≠ Term.HeadCtor.listElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.optionMatch ∧
      someTerm.headCtor ≠ Term.HeadCtor.eitherMatch ∧
      someTerm.headCtor ≠ Term.HeadCtor.idJ ∧
      someTerm.headCtor ≠ Term.HeadCtor.modElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.pathApp ∧
      someTerm.headCtor ≠ Term.HeadCtor.glueElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.recordProj ∧
      someTerm.headCtor ≠ Term.HeadCtor.refineElim) :
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
  -- Conditional eliminators are excluded by `notConditionalElim`.
  | app _ _ => exact absurd rfl notConditionalElim.1
  | appPi _ _ => exact absurd rfl notConditionalElim.2.1
  | fst _ => exact absurd rfl notConditionalElim.2.2.1
  | snd _ => exact absurd rfl notConditionalElim.2.2.2.1
  | boolElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.1
  | natElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.1
  | natRec _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.1
  | listElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.1
  | optionMatch _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.1
  | eitherMatch _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.1
  | idJ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.1
  | modElim _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.1
  | pathApp _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.1
  | glueElim _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | recordProj _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | refineElim _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end LeanFX2
