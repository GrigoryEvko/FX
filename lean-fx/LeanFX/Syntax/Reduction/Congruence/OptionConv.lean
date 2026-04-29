import LeanFX.Syntax.Reduction.Congruence.List

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Option Conv congruences (mirror the list versions). -/

/-- Definitional equivalence threads through `Term.optionSome`'s value. -/
theorem Conv.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} (h : Conv value₁ value₂) :
    Conv (Term.optionSome value₁) (Term.optionSome value₂) :=
  Conv.mapStep
    (fun value => Term.optionSome value)
    (fun singleStep => Step.optionSomeValue singleStep)
    h

/-- Definitional equivalence threads through `optionMatch`'s scrutinee. -/
theorem Conv.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch someBranch)
         (Term.optionMatch scrutinee₂ noneBranch someBranch) :=
  Conv.mapStep
    (fun scrutinee => Term.optionMatch scrutinee noneBranch someBranch)
    (fun singleStep => Step.optionMatchScrutinee singleStep)
    h

/-- Definitional equivalence threads through `optionMatch`'s none-branch. -/
theorem Conv.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv noneBranch₁ noneBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch₁ someBranch)
         (Term.optionMatch scrutinee noneBranch₂ someBranch) :=
  Conv.mapStep
    (fun noneBranch => Term.optionMatch scrutinee noneBranch someBranch)
    (fun singleStep => Step.optionMatchNone singleStep)
    h

/-- Definitional equivalence threads through `optionMatch`'s some-branch. -/
theorem Conv.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch someBranch₁)
         (Term.optionMatch scrutinee noneBranch someBranch₂) :=
  Conv.mapStep
    (fun someBranch => Term.optionMatch scrutinee noneBranch someBranch)
    (fun singleStep => Step.optionMatchSome singleStep)
    h

/-- Definitional equivalence threads through all three `optionMatch` positions. -/
theorem Conv.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_none : Conv noneBranch₁ noneBranch₂)
    (h_some : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
         (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  Conv.trans
    (Conv.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (Conv.trans
      (Conv.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (Conv.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))


end LeanFX.Syntax
