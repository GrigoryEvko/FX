import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Typed.ClassifierLevelMeasure
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/DenoteKeyedBoundedFundamentalMotive
    — the bounded fundamental theorem's conclusion motive + the two LEAF arms (#753 toward SN-043)

The bound-carrying analogue of `DenoteKeyedFundamentalMotive.lean` (`FundamentalConclusionAtDenote` + the `var` /
`universeFormation` leaf arms), built over the universe-label-AWARE `ReducibleTypeAtBounded` instead of the
label-blind `ReducibleTypeAtDenote`.  This is the brick where the bounded FT begins replacing the denote FT: the
denote FT's one open hole (the non-uniform `genFormationPi` `piReducibleAsType`, #752) is MODEL-OBSTRUCTED in the
denote relation (`DenoteKeyedCumulativityObstruction`), and the obstruction file itself names the fix — "a
STRENGTHENED reducibility whose universe MEMBERS carry a universe bound, re-proving CR1/CR2/CR3 and every FT arm".
The bounded relation is that strengthening (CR1/2/3 already unconditional); this file is the first FT arms.

## The motive — single uniform bound

`FundamentalConclusionAtBounded env bound context subject classifier`: under a closing substitution and a
bound-reducible environment `ReducibleEnvAtBounded env bound context`, the substituted subject is a bound-reducible
member of the substituted classifier, all at ONE uniform `bound`.  Same single-parameter shape as
`FundamentalConclusionAtDenote` (the relation's level-stability lets one bound carry the whole judgment, the binder
`cons` threading the same bound via `ReducibleEnvAtBounded.cons`).  The ambient `bound` must exceed every decoded
universe level appearing — the `belowBound` side conditions surface that locally; the FT assembly discharges them at
a large-enough bound (`ClassifierLevelMeasure.denote_lt_lsucc`).

## The leaf arms + bounded universe-membership machinery

  * `universeCode_isReducibleAtBounded` — `Type@e` is a bound-reducible TYPE (gate `denote e < bound`); the bounded
    `universeCode` arm carries the gate (unlike the ungated denote arm).
  * `universeMembershipBounded_levelIrrelevant` — the candidate of `Type@e` at `bound` (gate `denote e < bound`) is
    `fun member => SN member ∧ IsReducibleTypeAtBounded env (denote e env) member`, via the shipped coherence
    `denoteBelowFamilyBounded_eq_reducible` reassembled through `ofPointwiseIff` (pointwise iff — funext-free).
  * `universeFormationMemberAtBounded` / `…UnderClosingSubstitution` — `Type@e` is a bound-reducible MEMBER of
    `Type@(lsucc e)` (member side of no-Type-in-Type); the new gate vs. denote is the third component's
    `denote e < denote (lsucc e)` (`denote_lt_lsucc`), since `universeCode_isReducibleAtBounded` needs it.
  * `fundamentalVarAtBounded` — a variable concludes via `ReducibleEnvAtBounded.lookupReducible` (the substituted
    variable is `substitution index` definitionally, so the lookup IS the goal).
  * `fundamentalUniverseFormationAtBounded` — the universeFormation FT arm, via the substitution-shaped member.

## Zero-axiom verification

`var` is `ReducibleEnvAtBounded.lookupReducible`; the universe lemmas reuse the shipped bounded coherence +
`ofPointwiseIff` + `denote_lt_lsucc` + `noStep_universeCode`.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **`Type@levelExpr` is a bound-reducible TYPE at `bound`** (gate `denote levelExpr env < bound`).  The bounded
analogue of `universeCode_isReducibleAtDenote`; the bounded `universeCode` arm carries the `belowBound` gate, so
unlike the ungated denote arm this lemma takes the gate as a hypothesis. -/
theorem universeCode_isReducibleAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsReducibleTypeAtBounded (scope := scope) env bound
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨_, ReducibleTypeStepBounded.universeCode levelExpr flag belowBound⟩

/-- **Bounded universe-membership level-irrelevance.**  At any `bound` strictly above the decoded level
`denote levelExpr env`, the candidate of `Type@levelExpr` is `SN ∧ IsReducibleTypeAtBounded env (denote levelExpr
env)` — the bound-aware analogue of `universeMembership_levelIrrelevant`.  The bounded `universeCode` arm carries
the gate; coherence (`denoteBelowFamilyBounded_eq_reducible`) rewrites the below-family at `denote levelExpr env`
to the bounded relation there, reassembled through `ofPointwiseIff` (pointwise iff — no `funext`/`Quot.sound`). -/
theorem universeMembershipBounded_levelIrrelevant {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    ReducibleTypeAtBounded (scope := scope) env bound
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) member) := by
  have key : denoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env)
      = ReducibleTypeAtBounded (scope := scope) env (LevelExpr.denote levelExpr env) :=
    denoteBelowFamilyBounded_eq_reducible env bound (LevelExpr.denote levelExpr env) belowBound
  refine ReducibleTypeStepBounded.ofPointwiseIff
    (ReducibleTypeStepBounded.universeCode levelExpr flag belowBound) (fun member => ?_)
  show (IsStronglyNormalizing member ∧
      ∃ candidate, denoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env) member candidate)
    ↔ (IsStronglyNormalizing member ∧
      IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) member)
  rw [key]
  exact Iff.rfl

/-- **The bounded universeFormation MEMBER.**  `Type@levelExpr` is a bound-reducible member (at any `bound` strictly
above `denote (lsucc levelExpr) env`) of its classifier `Type@(lsucc levelExpr)` — the bound-aware member side of
no-Type-in-Type.  The witnessing candidate is the bounded universe candidate decoding at the fixed classifier level;
the member obligations are SN of the universe code (a normal form) and its bound-reducibility as a type at that
classifier level — the latter via `universeCode_isReducibleAtBounded`, whose gate `denote levelExpr env <
denote (lsucc levelExpr) env` is `denote_lt_lsucc`. -/
theorem universeFormationMemberAtBounded {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (bound : Nat)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
    IsReducibleMemberAtBounded (scope := scope) env bound
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtBounded env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) member,
    universeMembershipBounded_levelIrrelevant env bound (LevelExpr.lsucc levelExpr) flag belowBound,
    isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)),
    universeCode_isReducibleAtBounded env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) levelExpr flag
      (denote_lt_lsucc levelExpr env)⟩

/-- **The bounded universeFormation member under a closing substitution (FT shape).**  The universe codes are
closed (`childNil`), so the closing substitution leaves both `Type@levelExpr` and `Type@(lsucc levelExpr)` fixed;
the goal reduces definitionally to `universeFormationMemberAtBounded`. -/
theorem universeFormationMemberUnderClosingSubstitutionBounded {scope targetScope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (bound : Nat)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound)
    (substitution : RawTermSubst scope targetScope) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil))
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)) := by
  show IsReducibleMemberAtBounded env bound
    (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
  exact universeFormationMemberAtBounded env levelExpr flag bound belowBound

/-- **The bounded fundamental-theorem conclusion (single uniform bound).**  Under a closing substitution and a
bound-reducible environment at the uniform `bound`, the substituted subject is a bound-reducible member of the
substituted classifier.  Single `bound` (not a per-variable vector): the bounded relation's level-stability lets
one bound carry the whole judgment, the binder threading the same bound. -/
def FundamentalConclusionAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
    ReducibleEnvAtBounded env bound context substitution →
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject)

/-- **The bounded `var` arm (leaf).**  A variable is a bound-reducible member of its looked-up type directly from
the environment: `ReducibleEnvAtBounded.lookupReducible` delivers exactly this, and `subst substitution
(variableCell index)` is `substitution index` definitionally, so the lookup IS the goal. -/
theorem fundamentalVarAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionAtBounded env bound context (variableCell index) (context.lookup index) := by
  intro _targetScope substitution envReducible
  exact ReducibleEnvAtBounded.lookupReducible envReducible index

/-- **The bounded `universeFormation` arm (leaf).**  `Type@levelExpr` is a bound-reducible member of
`Type@(lsucc levelExpr)` under the closing substitution — the member side of no-Type-in-Type at the bounded layer.
Reuses `universeFormationMemberUnderClosingSubstitutionBounded`; carries the `belowBound` side condition (ambient
bound above the decoded classifier level), discharged by the FT at a large-enough bound. -/
theorem fundamentalUniverseFormationAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
    FundamentalConclusionAtBounded env bound context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _envReducible
  exact universeFormationMemberUnderClosingSubstitutionBounded env levelExpr flag bound belowBound substitution

end FX1Poly.Typed
