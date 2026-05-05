import LeanFX2.Lean.Kernel.Substitution

/-! # Lean/Kernel/Reduction

Lean kernel expression reduction.

## Deliverable

This module starts the encoded Lean-kernel reduction relation with the
load-bearing, substitution-sensitive rules:

* beta reduction for lambda application;
* zeta reduction for let expressions;
* metadata erasure.

The remaining Lean rules from the Day 8 plan (eta, delta, iota, projection,
quotient, and literal computation) need environment and inductive encodings and
are intentionally left to later slices.
-/

namespace LeanFX2
namespace LeanKernel

/-- One-step reduction for the encoded Lean kernel expression fragment. -/
inductive Step {level scope : Nat} :
    Expr level scope → Expr level scope → Prop
  /-- Beta: applying a lambda instantiates its body with the argument. -/
  | betaStep
      {binderName : Name}
      {domainExpr argumentExpr : Expr level scope}
      {bodyExpr : Expr level (scope + 1)}
      {binderInfo : BinderInfo} :
      Step
        (Expr.app
          (Expr.lam binderName domainExpr bodyExpr binderInfo)
          argumentExpr)
        (Expr.instantiate bodyExpr argumentExpr)
  /-- Zeta: a let expression instantiates its body with the let value. -/
  | zetaStep
      {declName : Name}
      {typeExpr valueExpr : Expr level scope}
      {bodyExpr : Expr level (scope + 1)}
      {nondep : Bool} :
      Step
        (Expr.letE declName typeExpr valueExpr bodyExpr nondep)
        (Expr.instantiate bodyExpr valueExpr)
  /-- Metadata nodes are computationally transparent. -/
  | metadataStep
      {metadata : MData}
      {bodyExpr : Expr level scope} :
      Step (Expr.mdata metadata bodyExpr) bodyExpr

namespace Step

/-- Beta against the newest bound variable reduces exactly to the argument.

This theorem is a wiring smoke: it compiles only if `Expr.instantiate` maps the
newest binder to the substituting expression. -/
theorem betaStep_newest_bvar {level scope : Nat}
    {binderName : Name}
    {domainExpr argumentExpr : Expr level scope}
    {binderInfo : BinderInfo} :
    Step
      (Expr.app
        (Expr.lam binderName domainExpr
          (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
          binderInfo)
        argumentExpr)
      argumentExpr := by
  change Step
    (Expr.app
      (Expr.lam binderName domainExpr
        (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
        binderInfo)
      argumentExpr)
    (Expr.instantiate
      (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
      argumentExpr)
  exact Step.betaStep

/-- Beta against an older bound variable lowers that variable by one binder.

This theorem catches the other common de Bruijn bug: confusing the newest
variable with a weakened outer variable. -/
theorem betaStep_succ_bvar {level scope : Nat}
    {binderName : Name}
    {domainExpr argumentExpr : Expr level scope}
    {binderInfo : BinderInfo}
    (position : Fin scope) :
    Step
      (Expr.app
        (Expr.lam binderName domainExpr
          (Expr.bvar (Fin.succ position))
          binderInfo)
        argumentExpr)
      (Expr.bvar position) := by
  cases position with
  | mk index isLt =>
      change Step
        (Expr.app
          (Expr.lam binderName domainExpr
            (Expr.bvar (Fin.succ ⟨index, isLt⟩))
            binderInfo)
          argumentExpr)
        (Expr.instantiate
          (Expr.bvar (Fin.succ ⟨index, isLt⟩))
          argumentExpr)
      exact Step.betaStep

/-- Zeta against the newest bound variable reduces exactly to the let value. -/
theorem zetaStep_newest_bvar {level scope : Nat}
    {declName : Name}
    {typeExpr valueExpr : Expr level scope}
    {nondep : Bool} :
    Step
      (Expr.letE declName typeExpr valueExpr
        (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
        nondep)
      valueExpr := by
  change Step
    (Expr.letE declName typeExpr valueExpr
      (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
      nondep)
    (Expr.instantiate
      (Expr.bvar ⟨0, Nat.zero_lt_succ scope⟩)
      valueExpr)
  exact Step.zetaStep

end Step

end LeanKernel
end LeanFX2
