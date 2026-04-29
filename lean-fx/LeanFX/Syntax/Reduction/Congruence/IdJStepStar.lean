import LeanFX.Syntax.Reduction.Congruence.EitherStepStar

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## idJ StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.idJ`'s baseCase. -/
theorem StepStar.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd)) :
    StepStar baseCase₁ baseCase₂ →
    StepStar (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJBase s)
        (StepStar.idJ_cong_base witness rest)

/-- Multi-step reduction threads through `Term.idJ`'s witness. -/
theorem StepStar.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)} :
    StepStar witness₁ witness₂ →
    StepStar (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJWitness baseCase s)
        (StepStar.idJ_cong_witness baseCase rest)

/-- Multi-step reduction threads through both positions of `Term.idJ`. -/
theorem StepStar.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : StepStar baseCase₁ baseCase₂)
    (h_witness : StepStar witness₁ witness₂) :
    StepStar (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  StepStar.trans
    (StepStar.idJ_cong_base witness₁ h_base)
    (StepStar.idJ_cong_witness baseCase₂ h_witness)



end LeanFX.Syntax
