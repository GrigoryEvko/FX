import LeanFX.Syntax.Reduction.Congruence.EitherConv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## idJ Conv congruences. -/

/-- Definitional equivalence threads through `Term.idJ`'s baseCase. -/
theorem Conv.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd))
    (h : Conv baseCase₁ baseCase₂) :
    Conv (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness) :=
  Conv.mapStep
    (fun baseCase => Term.idJ baseCase witness)
    (fun singleStep => Step.idJBase singleStep)
    h

/-- Definitional equivalence threads through `Term.idJ`'s witness. -/
theorem Conv.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂) :=
  Conv.mapStep
    (fun witness => Term.idJ baseCase witness)
    (fun singleStep => Step.idJWitness baseCase singleStep)
    h

/-- Definitional equivalence threads through both `Term.idJ` positions. -/
theorem Conv.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : Conv baseCase₁ baseCase₂)
    (h_witness : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  Conv.trans
    (Conv.idJ_cong_base witness₁ h_base)
    (Conv.idJ_cong_witness baseCase₂ h_witness)


end LeanFX.Syntax
