import LeanFX.Syntax.Reduction.Congruence.Bool

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Natural-number reduction congruences.

Multi-step and definitional-equivalence threading through `Term.natSucc`
and `Term.natElim`'s three positions, mirroring the boolean section. -/

/-- Definitional equivalence threads through `Term.natSucc`. -/
theorem Conv.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat}
    (h : Conv pred₁ pred₂) :
    Conv (Term.natSucc pred₁) (Term.natSucc pred₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natSuccPred s)

/-- Definitional equivalence threads through `natElim`'s scrutinee. -/
theorem Conv.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch succBranch)
         (Term.natElim scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimScrutinee s)

/-- Definitional equivalence threads through `natElim`'s zero-branch. -/
theorem Conv.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch₁ succBranch)
         (Term.natElim scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimZero s)

/-- Definitional equivalence threads through `natElim`'s succ-branch. -/
theorem Conv.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch succBranch₁)
         (Term.natElim scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimSucc s)

/-- Definitional equivalence threads through all three `natElim` positions. -/
theorem Conv.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec Conv congruences (parallel to natElim, with the richer
succBranch type `Ty.arrow Ty.nat (Ty.arrow resultType resultType)`). -/

/-- Definitional equivalence threads through `natRec`'s scrutinee. -/
theorem Conv.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch succBranch)
         (Term.natRec scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecScrutinee s)

/-- Definitional equivalence threads through `natRec`'s zero-branch. -/
theorem Conv.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch₁ succBranch)
         (Term.natRec scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecZero s)

/-- Definitional equivalence threads through `natRec`'s succ-branch. -/
theorem Conv.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch succBranch₁)
         (Term.natRec scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecSucc s)

/-- Definitional equivalence threads through all three `natRec` positions. -/
theorem Conv.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))


end LeanFX.Syntax
