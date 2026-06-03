import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/DenoteKeyedUniverseFormationMember
    — the denote fundamental theorem's universeFormation arm (route D leaf brick)

The cleanest leaf arm of the denote-keyed fundamental theorem: the universe code `Type@levelExpr` is a
denote-reducible MEMBER (at any ambient level strictly above `denote (lsucc levelExpr) env`) of its classifier
`Type@(lsucc levelExpr)`.  This is the denote-layer universe hierarchy / no-Type-in-Type at the membership
level: a universe sits one decoded step below the universe that classifies it, and that membership is witnessed
by the level-irrelevant candidate from `DenoteKeyedReducibility`.

It composes exactly three already-shipped facts, with no new induction:

  * `universeMembership_levelIrrelevant` supplies the candidate of `Type@(lsucc levelExpr)` above its decoded
    level — `fun member => IsStronglyNormalizing member ∧ IsReducibleTypeAtDenote env (denote (lsucc
    levelExpr) env) member` — the witness `ReducibleTypeAtDenote` for the classifier;
  * `isStronglyNormalizing_of_noStep` + `noStep_universeCode` discharge the SN conjunct (`Type@levelExpr` is a
    normal form — no `Step` fires from a `gen_universeCode` cell);
  * `universeCode_isReducibleAtDenote` discharges the reducible-type conjunct (`Type@levelExpr` is a reducible
    type at the fixed classifier level `denote (lsucc levelExpr) env`).

The classifier's decoded level is `denote (lsucc levelExpr) env`; the member candidate decodes at that fixed
level (independent of the ambient `level`), so the membership is stable — the whole point of the denote
reformulation versus the drifting fuel model.

## Zero-axiom verification

The proof is a single anonymous-constructor term: `⟨candidate, classifierReducible, memberSN, memberReducible⟩`,
flattening the `∃ candidate, ReducibleTypeAtDenote … ∧ (IsStronglyNormalizing … ∧ IsReducibleTypeAtDenote …)`
of `IsReducibleMemberAtDenote`.  No tactic, no `match`, no recursion — it inherits the zero-axiom status of its
three components.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The denote fundamental theorem's universeFormation arm.**  The universe code `Type@levelExpr` is a
denote-reducible member (at any ambient `level` strictly above `denote (lsucc levelExpr) env`) of its classifier
`Type@(lsucc levelExpr)`.  The witnessing candidate is the level-irrelevant universe candidate decoding at the
fixed classifier level `denote (lsucc levelExpr) env`; the member obligations are SN of the universe code (a
normal form) and its reducibility as a type at that classifier level. -/
theorem universeFormationMemberAtDenote {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level) :
    IsReducibleMemberAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) member,
    universeMembership_levelIrrelevant env level (LevelExpr.lsucc levelExpr) flag levelAbove,
    isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)),
    universeCode_isReducibleAtDenote env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) levelExpr flag⟩

/-- **The denote universeFormation member arm under a closing substitution (the fundamental-theorem shape).**
The universe codes are closed (`childNil`), so the closing substitution leaves both the subject `Type@levelExpr`
and its classifier `Type@(lsucc levelExpr)` fixed (`subst σ` is `rfl` on them); the goal therefore reduces
definitionally to `universeFormationMemberAtDenote`.  This is the FT's universe-formation case under the closing
substitution — the member side of no-Type-in-Type, completing the member-arm-under-substitution leaf set
(var / conv / Π-elimination / universeFormation). -/
theorem universeFormationMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level)
    (substitution : RawTermSubst scope targetScope) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil))
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)) := by
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
  exact universeFormationMemberAtDenote env levelExpr flag level levelAbove

end FX1Poly.Typed
