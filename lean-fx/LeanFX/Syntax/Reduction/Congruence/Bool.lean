import LeanFX.Syntax.Reduction.Congruence.Basic

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Boolean reduction congruences.

Multi-step and definitional-equivalence threading through `boolElim`'s
three positions, plus combined three-position congruences. -/

/-- Multi-step reduction threads through `boolElim`'s scrutinee. -/
theorem StepStar.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.boolElim scrutinee₁ thenBr elseBr)
             (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimScrutinee s)
        (StepStar.boolElim_cong_scrutinee thenBr elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s then-branch. -/
theorem StepStar.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    StepStar thenBr₁ thenBr₂ →
    StepStar (Term.boolElim scrutinee thenBr₁ elseBr)
             (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimThen s)
        (StepStar.boolElim_cong_then scrutinee elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s else-branch. -/
theorem StepStar.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    StepStar elseBr₁ elseBr₂ →
    StepStar (Term.boolElim scrutinee thenBr elseBr₁)
             (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimElse s)
        (StepStar.boolElim_cong_else scrutinee thenBr rest)

/-- Multi-step reduction threads through all three `boolElim`
positions simultaneously.  Sequenced via three `trans` calls over
the single-position congruences. -/
theorem StepStar.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_then : StepStar thenBr₁ thenBr₂)
    (h_else : StepStar elseBr₁ elseBr₂) :
    StepStar (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
             (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  StepStar.trans
    (StepStar.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (StepStar.trans
      (StepStar.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (StepStar.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-- Definitional equivalence threads through `boolElim`'s scrutinee. -/
theorem Conv.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    Conv scrutinee₁ scrutinee₂ →
    Conv (Term.boolElim scrutinee₁ thenBr elseBr)
         (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_scrutinee thenBr elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₁)
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimScrutinee s)

/-- Definitional equivalence threads through `boolElim`'s then-branch. -/
theorem Conv.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    Conv thenBr₁ thenBr₂ →
    Conv (Term.boolElim scrutinee thenBr₁ elseBr)
         (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_then scrutinee elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_then scrutinee elseBr h₁)
        (Conv.boolElim_cong_then scrutinee elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimThen s)

/-- Definitional equivalence threads through `boolElim`'s else-branch. -/
theorem Conv.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    Conv elseBr₁ elseBr₂ →
    Conv (Term.boolElim scrutinee thenBr elseBr₁)
         (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_else scrutinee thenBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_else scrutinee thenBr h₁)
        (Conv.boolElim_cong_else scrutinee thenBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimElse s)

/-- Definitional equivalence threads through all three `boolElim`
positions simultaneously. -/
theorem Conv.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_then : Conv thenBr₁ thenBr₂)
    (h_else : Conv elseBr₁ elseBr₂) :
    Conv (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
         (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  Conv.trans
    (Conv.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (Conv.trans
      (Conv.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (Conv.boolElim_cong_else scrutinee₂ thenBr₂ h_else))


end LeanFX.Syntax
