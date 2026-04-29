import LeanFX.Syntax.Reduction.Congruence.OptionStepStar

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Either StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.eitherInl`. -/
theorem StepStar.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInl (rightType := rightType) value₁)
             (Term.eitherInl (rightType := rightType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInlValue s)
        (StepStar.eitherInl_cong rest)

/-- Multi-step reduction threads through `Term.eitherInr`. -/
theorem StepStar.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInr (leftType := leftType) value₁)
             (Term.eitherInr (leftType := leftType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInrValue s)
        (StepStar.eitherInr_cong rest)

/-- Multi-step reduction threads through `eitherMatch`'s scrutinee. -/
theorem StepStar.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
             (Term.eitherMatch scrutinee₂ leftBranch rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchScrutinee s)
        (StepStar.eitherMatch_cong_scrutinee leftBranch rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s left-branch. -/
theorem StepStar.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar leftBranch₁ leftBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
             (Term.eitherMatch scrutinee leftBranch₂ rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchLeft s)
        (StepStar.eitherMatch_cong_left scrutinee rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s right-branch. -/
theorem StepStar.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)} :
    StepStar rightBranch₁ rightBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch rightBranch₁)
             (Term.eitherMatch scrutinee leftBranch rightBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchRight s)
        (StepStar.eitherMatch_cong_right scrutinee leftBranch rest)

/-- Multi-step reduction threads through all three `eitherMatch` positions. -/
theorem StepStar.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_left : StepStar leftBranch₁ leftBranch₂)
    (h_right : StepStar rightBranch₁ rightBranch₂) :
    StepStar (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
             (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  StepStar.trans
    (StepStar.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (StepStar.trans
      (StepStar.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (StepStar.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))


end LeanFX.Syntax
