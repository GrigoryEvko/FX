prelude
import LeanFX2.FX1.LeanKernel.Substitution

/-! # FX1/LeanKernel/Reduction

Lean kernel expression reduction.

## Deliverable

This module starts the encoded Lean-kernel reduction relation with the
load-bearing, substitution-sensitive rules:

* beta reduction for lambda application;
* eta reduction for lambda over weakened function application;
* zeta reduction for let expressions;
* metadata erasure.

The remaining Lean rules from the Day 8 plan (delta, iota, projection,
quotient, and literal computation) need environment and inductive encodings and
are intentionally left to later slices.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- One-step reduction for the encoded Lean kernel expression fragment. -/
inductive Step {level scope : Nat} :
    Expr level scope → Expr level scope → Prop
  /-- Beta: applying a lambda instantiates its body with the argument. -/
  | betaStep
      {binderName : Name}
      {domainExpr argumentExpr : Expr level scope}
      {bodyExpr : Expr level (Nat.succ scope)}
      {binderInfo : BinderInfo} :
      Step
        (Expr.app
          (Expr.lam binderName domainExpr bodyExpr binderInfo)
          argumentExpr)
        (Expr.instantiate bodyExpr argumentExpr)
  /-- Eta: a lambda whose body applies a weakened function to the newest
  binder reduces to the unweakened function.  The side condition "the
  bound variable does not occur free in `fnExpr`" is captured structurally
  by `Expr.weaken`: weakening shifts free variables upward, so the
  newest binder `Expr.bvar 0` never appears free inside `Expr.weaken
  fnExpr`.  Mirrors Lean's kernel η rule in `type_checker.cpp`. -/
  | etaStep
      {binderName : Name}
      {domainExpr fnExpr : Expr level scope}
      {binderInfo : BinderInfo} :
      Step
        (Expr.lam binderName domainExpr
          (Expr.app
            (Expr.weaken fnExpr)
            (Expr.bvar (level := level) (scope := Nat.succ scope) Nat.zero))
          binderInfo)
        fnExpr
  /-- Zeta: a let expression instantiates its body with the let value. -/
  | zetaStep
      {declName : Name}
      {typeExpr valueExpr : Expr level scope}
      {bodyExpr : Expr level (Nat.succ scope)}
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
          (Expr.bvar (level := level) (scope := Nat.succ scope) Nat.zero)
          binderInfo)
        argumentExpr)
      argumentExpr :=
  Step.betaStep

/-- Beta against an older bound variable lowers that variable by one binder.

This theorem catches the other common de Bruijn bug: confusing the newest
variable with a weakened outer variable. -/
theorem betaStep_succ_bvar {level scope : Nat}
    {binderName : Name}
    {domainExpr argumentExpr : Expr level scope}
    {binderInfo : BinderInfo}
    (position : Nat) :
    Step
      (Expr.app
        (Expr.lam binderName domainExpr
          (Expr.bvar (level := level) (scope := Nat.succ scope)
            (Nat.succ position))
          binderInfo)
        argumentExpr)
      (Expr.bvar (level := level) (scope := scope) position) :=
  Step.betaStep

/-- Zeta against the newest bound variable reduces exactly to the let value. -/
theorem zetaStep_newest_bvar {level scope : Nat}
    {declName : Name}
    {typeExpr valueExpr : Expr level scope}
    {nondep : Bool} :
    Step
      (Expr.letE declName typeExpr valueExpr
        (Expr.bvar (level := level) (scope := Nat.succ scope) Nat.zero)
        nondep)
      valueExpr :=
  Step.zetaStep

/-- Eta on a constant-headed body: `lam x. (const name levels) x` reduces
to `const name levels`.  This smoke exercises the structural side of η —
`Expr.weaken (Expr.const constName levels)` reduces definitionally to
`Expr.const constName levels` at the wider scope (constants carry no
bound variables), so the η constructor unifies with the source. -/
theorem etaStep_const_body {level scope : Nat}
    {binderName constName : Name}
    {domainExpr : Expr level scope}
    {levels : List Level}
    {binderInfo : BinderInfo} :
    Step
      (Expr.lam binderName domainExpr
        (Expr.app
          (Expr.const (level := level) (scope := Nat.succ scope)
            constName levels)
          (Expr.bvar (level := level) (scope := Nat.succ scope) Nat.zero))
        binderInfo)
      (Expr.const (level := level) (scope := scope) constName levels) :=
  Step.etaStep
    (fnExpr := Expr.const (level := level) (scope := scope) constName levels)

/-- Eta on a bvar-headed body: `lam x. (bvar (k+1)) (bvar 0)` reduces to
`bvar k`.  This smoke exercises the de Bruijn side of η —
`Expr.weaken (Expr.bvar k)` reduces definitionally to
`Expr.bvar (Nat.succ k)` via `ExprRenaming.weaken position = Nat.succ
position`, so the outer-binder reference shifts as expected and the η
constructor unifies with the source. -/
theorem etaStep_bvar_body {level scope : Nat}
    {binderName : Name}
    {domainExpr : Expr level scope}
    {binderInfo : BinderInfo}
    (outerPosition : Nat) :
    Step
      (Expr.lam binderName domainExpr
        (Expr.app
          (Expr.bvar (level := level) (scope := Nat.succ scope)
            (Nat.succ outerPosition))
          (Expr.bvar (level := level) (scope := Nat.succ scope) Nat.zero))
        binderInfo)
      (Expr.bvar (level := level) (scope := scope) outerPosition) :=
  Step.etaStep
    (fnExpr := Expr.bvar (level := level) (scope := scope) outerPosition)

end Step

end FX1.LeanKernel
end LeanFX2
