import FX1Poly.Typed.ClassifierLevelDiagnosis
import FX1Poly.Core.StratifiedReducibleTypeNeutral
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Typed/ClassifierLevelMeasure
    — SN-003: the predicative well-founded measure for classifier-level reducibility + non-degenerate base

SN-002 (`ClassifierLevelDiagnosis`) gave the GO verdict that the reducibility level can be re-keyed to the
classifier universe level `LevelExpr.denote`.  A well-founded recursion on that level needs TWO measure
facts, plus a non-degenerate base; this file lands all three, zero-axiom.

* **Predicative strict decrease (`denote_lt_lsucc`).**  `denote e env < denote (lsucc e) env` — the
  universe-DECODE step strictly lowers the level: a member of `Type@(lsucc e)` decodes to a reducible type
  at `denote e env < denote (lsucc e) env`.  Immediate from `denote_lsucc` (`denote (lsucc e) env =
  denote e env + 1`) + `Nat.lt_succ_self`.  This is THE measure the denote-keyed recursion descends on at
  the universe arm.

* **Former-component bound (`denote_le_lmax_left` / `denote_le_lmax_right`).**  A Π/Σ former
  `Π(x:A).B : Type@(lmax (levelA) (levelB))` combines its component levels by `lmax`; each component is
  `≤` the former's level (`denote eᵢ env ≤ denote (lmax e1 e2) env`).  So the recursion may descend into
  the domain/codomain without INCREASING the measure (the strict decrease comes from the decode step
  above; the former arm is non-increasing).  Proved via the structural `LevelExpr.levelMax` bound
  (`levelMax_le_{left,right}`, private here — `levelMax` is the custom structural max, not `Nat.max`).

* **Non-degenerate base (`variableCell_reducibleTypeAtZero`).**  Unlike the artificially-EMPTY universe
  membership at fuel 0 (`RouteAObstruction`, SN-001), the base level is GENUINELY inhabited for
  NEUTRAL/base types: a variable is a reducible TYPE at level 0 via the level-independent `neutral` arm,
  with the inhabited `IsStronglyNormalizing` candidate.  The shipped
  `IsReducibleMemberAt.variableClassifierHasVariableMemberAtZero` is the member-side companion (a neutral
  classifier HAS a member at 0).  Together they LOCATE the SN-001 degeneracy precisely: it is confined to
  the universe CODE's membership, not to neutral types — exactly why the classifier-level model (whose base
  is the neutral fragment) escapes the fuel-0 vacuity.

## Zero-axiom verification

`denote_lt_lsucc` is `Nat.lt_succ_self` through the `denote_lsucc` defeq; the `lmax` bounds are structural
`Nat` inductions (`Nat.zero_le` / `Nat.le_refl` / `Nat.succ_le_succ`, no `omega`); the base witness is the
`ReducibleTypeStep.neutral` constructor with the variable's `noWeakHeadStep` + two `decide`d root
inequalities.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated
per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- `valueA ≤ levelMax valueA valueB` for the custom structural `LevelExpr.levelMax` (`= max`), by
structural induction mirroring `levelMax`'s three clauses. -/
private theorem levelMax_le_left :
    ∀ (valueA valueB : Nat), valueA ≤ LevelExpr.levelMax valueA valueB
  | 0, _ => Nat.zero_le _
  | _ + 1, 0 => Nat.le_refl _
  | valueA + 1, valueB + 1 => Nat.succ_le_succ (levelMax_le_left valueA valueB)

/-- `valueB ≤ levelMax valueA valueB` — the right component bound, dual of `levelMax_le_left`. -/
private theorem levelMax_le_right :
    ∀ (valueA valueB : Nat), valueB ≤ LevelExpr.levelMax valueA valueB
  | 0, _ => Nat.le_refl _
  | _ + 1, 0 => Nat.zero_le _
  | valueA + 1, valueB + 1 => Nat.succ_le_succ (levelMax_le_right valueA valueB)

/-- **Predicative strict decrease (the universe-decode measure step).**  The denoted classifier level
strictly decreases across a universe successor: `denote e env < denote (lsucc e) env`, since
`denote (lsucc e) env = denote e env + 1`.  This is the strictly-decreasing measure the denote-keyed
reducibility recursion uses at the universe arm (member at `Type@(lsucc e)` ⟶ reducible type at the
strictly smaller `denote e env`). -/
theorem denote_lt_lsucc (e : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote e env < LevelExpr.denote e.lsucc env :=
  Nat.lt_succ_self (LevelExpr.denote e env)

/-- **Former-component bound (left / domain).**  A component of an `lmax` former level is `≤` the former
level: `denote e1 env ≤ denote (lmax e1 e2) env`.  So the denote-keyed recursion may descend into a Π/Σ
former's DOMAIN (whose level is `e1`) without increasing the measure. -/
theorem denote_le_lmax_left (e1 e2 : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote e1 env ≤ LevelExpr.denote (LevelExpr.lmax e1 e2) env :=
  levelMax_le_left (LevelExpr.denote e1 env) (LevelExpr.denote e2 env)

/-- **Former-component bound (right / codomain).**  The dual: `denote e2 env ≤ denote (lmax e1 e2) env`,
so the recursion may descend into the CODOMAIN without increasing the measure. -/
theorem denote_le_lmax_right (e1 e2 : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote e2 env ≤ LevelExpr.denote (LevelExpr.lmax e1 e2) env :=
  levelMax_le_right (LevelExpr.denote e1 env) (LevelExpr.denote e2 env)

/-- **Non-degenerate base.**  A variable is a reducible TYPE at level 0, with the inhabited
`IsStronglyNormalizing` candidate (the level-independent `neutral` arm: a variable is weak-head normal and
neither Π- nor universe-rooted).  Contrast SN-001's `universeDomainPiVacuouslyReducibleAtZero` /
`IsReducibleMemberAt.universeCodeHasNoMemberAtZero`: the fuel-0 degeneracy is confined to the universe
CODE's membership — NEUTRAL types genuinely inhabit the base level (the member-side companion is the shipped
`IsReducibleMemberAt.variableClassifierHasVariableMemberAtZero`).  This is why a classifier-level model
whose base is the neutral fragment escapes the fuel-0 vacuity. -/
theorem variableCell_reducibleTypeAtZero {scope : Nat} (index : Fin scope) :
    IsReducibleTypeAt 0 (variableCell index) :=
  ⟨IsStronglyNormalizing,
    ReducibleTypeStep.neutral (IsNeutral.var index).noWeakHeadStep
      (by show Generator.gen_var ≠ Generator.gen_piTyCode; decide)
      (by show Generator.gen_var ≠ Generator.gen_universeCode; decide)⟩

end FX1Poly.Typed
