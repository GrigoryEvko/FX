import LeanFX.Syntax.Reduction.Congruence.NatStepStar

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Option StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.optionSome`. -/
theorem StepStar.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} :
    StepStar value₁ value₂ →
    StepStar (Term.optionSome value₁) (Term.optionSome value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionSomeValue s)
        (StepStar.optionSome_cong rest)

/-- Multi-step reduction threads through `optionMatch`'s scrutinee. -/
theorem StepStar.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.optionMatch scrutinee₁ noneBranch someBranch)
             (Term.optionMatch scrutinee₂ noneBranch someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchScrutinee s)
        (StepStar.optionMatch_cong_scrutinee noneBranch someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s none-branch. -/
theorem StepStar.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar noneBranch₁ noneBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch₁ someBranch)
             (Term.optionMatch scrutinee noneBranch₂ someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchNone s)
        (StepStar.optionMatch_cong_none scrutinee someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s some-branch. -/
theorem StepStar.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)} :
    StepStar someBranch₁ someBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch someBranch₁)
             (Term.optionMatch scrutinee noneBranch someBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchSome s)
        (StepStar.optionMatch_cong_some scrutinee noneBranch rest)

/-- Multi-step reduction threads through all three `optionMatch` positions. -/
theorem StepStar.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_none : StepStar noneBranch₁ noneBranch₂)
    (h_some : StepStar someBranch₁ someBranch₂) :
    StepStar (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
             (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  StepStar.trans
    (StepStar.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (StepStar.trans
      (StepStar.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (StepStar.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))


end LeanFX.Syntax
