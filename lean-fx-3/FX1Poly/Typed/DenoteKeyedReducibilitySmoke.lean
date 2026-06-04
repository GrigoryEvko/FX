import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/DenoteKeyedReducibilitySmoke
    — concrete denote-keyed reducibility witnesses (regression corpus, SN-149-flavored)

The denote-keyed reducibility relation (`ReducibleTypeStepDenote` / `IsReducibleTypeAtDenote`) and its
metatheory (anti-vacuity, level-irrelevance, the genFormationPi former engine) are all parameterized; until now
there was NO concrete witness exercising the relation on actual raw cells.  This file ships the first two — the
two LEAF cases of the step functor — guarding the load-bearing reducibility entry points against regression:

  * `smoke_universeCode_isReducibleAtDenote` — the `universeCode` arm: a universe code is a reducible type at
    EVERY ambient level (`universeCode_isReducibleAtDenote`, the anti-vacuity that refutes SN-001's empty fuel-0
    base — the universe code never has an empty candidate, in stark contrast to the fuel model).
  * `smoke_neutralVariable_isReducibleAtDenote` — the `neutral` arm: a context variable (a weak-head-normal
    non-Π non-universe code) is a reducible type at every level, with the strong-normalization candidate.  The
    `neutral` constructor's `noWeakHeadStep` premise is discharged from `noStep_var` via `WeakHeadStep.toStep`
    (a weak-head step embeds into a full step, which a variable has none of); the root-generator inequalities
    reduce `(.mkGen .gen_var ..).rootGenerator` to `gen_var` (a `show` to the closed goal, no free `index`) and
    `decide` the closed enum inequality.

Together they are the universe / neutral leaves of `ReducibleTypeStepDenote`; the remaining two arms
(`whnfExpand` head-expansion, `piType` dependent arrow) are exercised by the shipped former-reducibility lemmas.

## Zero-axiom verification

`smoke_universeCode_isReducibleAtDenote` is `universeCode_isReducibleAtDenote`; `smoke_neutralVariable` is one
`neutral` constructor with a `WeakHeadStep.toStep`∘`noStep_var` premise and two `show`-then-`decide` enum
inequalities.  No `funext`, no recursion.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Smoke: a universe code is denote-reducible at any level.**  The `universeCode` leaf — the anti-vacuity
refuting SN-001's empty fuel-0 base (the universe code is reducible with a non-empty candidate at EVERY level). -/
theorem smoke_universeCode_isReducibleAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  universeCode_isReducibleAtDenote env level levelExpr flag

/-- **Smoke: a context variable is denote-reducible at any level.**  The `neutral` leaf — a variable is
weak-head-normal (no `Step`, hence no `WeakHeadStep` via `WeakHeadStep.toStep`) and is neither Π- nor
universe-rooted, so the `neutral` arm fires with the strong-normalization candidate. -/
theorem smoke_neutralVariable_isReducibleAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    (index : Fin scope) :
    IsReducibleTypeAtDenote env level (.mkGen .gen_var index .childNil) :=
  ⟨IsStronglyNormalizing,
    ReducibleTypeStepDenote.neutral
      (fun _reduct weakHeadStep => noStep_var index weakHeadStep.toStep)
      (by show Generator.gen_var ≠ Generator.gen_piTyCode; decide)
      (by show Generator.gen_var ≠ Generator.gen_universeCode; decide)⟩

end FX1Poly.Typed
