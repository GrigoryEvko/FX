import LeanFX.Syntax.Reduction.Congruence.OptionConv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Either Conv congruences (mirror the option versions). -/

/-- Definitional equivalence threads through `Term.eitherInl`'s value. -/
theorem Conv.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInl (rightType := rightType) value₁)
         (Term.eitherInl (rightType := rightType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInlValue s)

/-- Definitional equivalence threads through `Term.eitherInr`'s value. -/
theorem Conv.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInr (leftType := leftType) value₁)
         (Term.eitherInr (leftType := leftType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInrValue s)

/-- Definitional equivalence threads through `eitherMatch`'s scrutinee. -/
theorem Conv.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
         (Term.eitherMatch scrutinee₂ leftBranch rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchScrutinee s)

/-- Definitional equivalence threads through `eitherMatch`'s left-branch. -/
theorem Conv.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv leftBranch₁ leftBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
         (Term.eitherMatch scrutinee leftBranch₂ rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchLeft s)

/-- Definitional equivalence threads through `eitherMatch`'s right-branch. -/
theorem Conv.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch rightBranch₁)
         (Term.eitherMatch scrutinee leftBranch rightBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchRight s)

/-- Definitional equivalence threads through all three `eitherMatch` positions. -/
theorem Conv.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_left : Conv leftBranch₁ leftBranch₂)
    (h_right : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
         (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  Conv.trans
    (Conv.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (Conv.trans
      (Conv.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (Conv.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))


end LeanFX.Syntax
