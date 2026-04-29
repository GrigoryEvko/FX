import LeanFX.Syntax.Reduction.Congruence.IdJConv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## StepStar congruences for nat (defined above the Conv versions
because Step.par.toStar consumes them). -/

/-- Multi-step reduction threads through `Term.natSucc`. -/
theorem StepStar.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat} :
    StepStar pred₁ pred₂ →
    StepStar (Term.natSucc pred₁) (Term.natSucc pred₂)
  :=
    StepStar.mapStep
      (fun predecessor => Term.natSucc predecessor)
      (fun singleStep => Step.natSuccPred singleStep)

/-- Multi-step reduction threads through `natElim`'s scrutinee. -/
theorem StepStar.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natElim scrutinee₁ zeroBranch succBranch)
             (Term.natElim scrutinee₂ zeroBranch succBranch)
  :=
    StepStar.mapStep
      (fun scrutinee => Term.natElim scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natElimScrutinee singleStep)

/-- Multi-step reduction threads through `natElim`'s zero-branch. -/
theorem StepStar.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch₁ succBranch)
             (Term.natElim scrutinee zeroBranch₂ succBranch)
  :=
    StepStar.mapStep
      (fun zeroBranch => Term.natElim scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natElimZero singleStep)

/-- Multi-step reduction threads through `natElim`'s succ-branch. -/
theorem StepStar.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch succBranch₁)
             (Term.natElim scrutinee zeroBranch succBranch₂)
  :=
    StepStar.mapStep
      (fun succBranch => Term.natElim scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natElimSucc singleStep)

/-- Multi-step reduction threads through all three `natElim` positions. -/
theorem StepStar.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec StepStar congruences (placed before Step.par.toStar
which consumes them, parallel to natElim). -/

/-- Multi-step reduction threads through `natRec`'s scrutinee. -/
theorem StepStar.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natRec scrutinee₁ zeroBranch succBranch)
             (Term.natRec scrutinee₂ zeroBranch succBranch)
  :=
    StepStar.mapStep
      (fun scrutinee => Term.natRec scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natRecScrutinee singleStep)

/-- Multi-step reduction threads through `natRec`'s zero-branch. -/
theorem StepStar.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch₁ succBranch)
             (Term.natRec scrutinee zeroBranch₂ succBranch)
  :=
    StepStar.mapStep
      (fun zeroBranch => Term.natRec scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natRecZero singleStep)

/-- Multi-step reduction threads through `natRec`'s succ-branch. -/
theorem StepStar.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch succBranch₁)
             (Term.natRec scrutinee zeroBranch succBranch₂)
  :=
    StepStar.mapStep
      (fun succBranch => Term.natRec scrutinee zeroBranch succBranch)
      (fun singleStep => Step.natRecSucc singleStep)

/-- Multi-step reduction threads through all three `natRec` positions. -/
theorem StepStar.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))


end LeanFX.Syntax
