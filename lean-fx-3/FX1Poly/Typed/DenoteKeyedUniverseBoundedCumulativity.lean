import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedUniverseBoundedCumulativity
    — the universe candidate is bound-independent BELOW the bound: the positive complement to the
      cumulativity obstruction, isolating the obstruction to the gap regime alone (toward #753/SN-D5e)

`DenoteKeyedCumulativityObstruction.lean` pins the NEGATIVE half: a gap-universe-domain Π
(`denote levelExpr env >= ambient`) is reducible at the low level only VACUOUSLY (empty member
candidate, `denoteBelowFamily_eq_empty_of_ge`), so its low-level reducibility is codomain-blind and
cannot lift — the within-model cumulativity is model-obstructed for the GAP regime.

This file ships the POSITIVE half: in the BOUNDED regime (`denote levelExpr env < ambient`), the
universe candidate IS level-stable, so cumulativity holds.  The mechanism is exactly the dual of the
obstruction's: `universeDenotePredicate env lowerAt levelExpr` reaches `lowerAt` only at the FIXED index
`denote levelExpr env`, and when that index is strictly below the ambient level, the below-family
coherence `denoteBelowFamily_eq_reducible` rewrites `denoteBelowFamily env level (denote levelExpr env)`
to the bound-INDEPENDENT `ReducibleTypeAtDenote env (denote levelExpr env)`.  So two ambient levels that
both exceed `denote levelExpr env` assign the universe the SAME member candidate.

Together with the obstruction witness, this pins the EXACT boundary of denote-keyed universe
cumulativity: it holds iff the universe sits strictly below the ambient level.  The gap regime is the
sole residual — precisely the case the bound-carrying refactor (#753) excludes by construction (a
bound-carrying universe arm fires only below the bound, so every universe it admits is in the regime
this file proves stable).  These lemmas are therefore the model-internal evidence that the bound-carrying
fix is sound: the candidate the bounded universe arm would carry is already proven level-stable here, over
the existing relation, with no new inductive and no re-proof of CR1/CR2/CR3.

## What lands here (all zero-axiom)

  * `universeDenoteCandidate_boundIndependent` — for `denote levelExpr env < lowerLevel` and `< higherLevel`,
    the universe member candidate at the two ambient levels is pointwise-equivalent (both rewrite to the
    reducibility relation at `denote levelExpr env`).
  * `universeReducible_withLowerCandidate_atHigher` — cumulativity below the bound: when
    `denote levelExpr env < lowerLevel <= higherLevel`, the universe is reducible-as-type at the HIGHER
    level carrying the LOWER level's candidate (same-candidate transport up, via `ofPointwiseIff`).

## Zero-axiom verification

Two `denoteBelowFamily_eq_reducible` rewrites + `Iff.rfl` for the bound-independence; the universe arm
constructor + `ofPointwiseIff` + `Nat.lt_of_lt_of_le` for the cumulativity.  No `funext` (the candidate
equivalence is pointwise), no induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The universe candidate is bound-independent below the bound.**  When the universe's decoded level is
strictly below BOTH ambient levels, its denote member candidate (which reaches `lowerAt` only at the fixed
index `denote levelExpr env`) rewrites — via the below-family coherence `denoteBelowFamily_eq_reducible` —
to the bound-independent `ReducibleTypeAtDenote env (denote levelExpr env)` at both levels.  The positive
resolution, at the CANDIDATE level, of the cumulativity obstruction
(`DenoteKeyedCumulativityObstruction`): the universe candidate only DRIFTS in the GAP regime (decoded
level `>=` ambient); below the bound it is stable. -/
theorem universeDenoteCandidate_boundIndependent {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (lowerLevel higherLevel : Nat)
    (belowLower : LevelExpr.denote levelExpr env < lowerLevel)
    (belowHigher : LevelExpr.denote levelExpr env < higherLevel)
    (typeCode : RawTerm scope) :
    universeDenotePredicate env (denoteBelowFamily env lowerLevel) levelExpr typeCode ↔
      universeDenotePredicate env (denoteBelowFamily env higherLevel) levelExpr typeCode := by
  simp only [universeDenotePredicate]
  rw [denoteBelowFamily_eq_reducible env lowerLevel (LevelExpr.denote levelExpr env) belowLower,
      denoteBelowFamily_eq_reducible env higherLevel (LevelExpr.denote levelExpr env) belowHigher]

/-- **Universe cumulativity below the bound (same-candidate transport up).**  When `denote levelExpr env <
lowerLevel <= higherLevel`, the universe `Type@levelExpr` is reducible-as-type at the HIGHER level carrying
the LOWER level's member candidate: the universe arm fires at the higher level (with the higher candidate),
then `ofPointwiseIff` swaps to the lower candidate via bound-independence.  This is the cumulativity the
obstruction said was missing — it holds precisely in the BOUNDED regime (universe below ambient),
isolating the genuine obstruction to the gap regime (`denote >= ambient`) ALONE. -/
theorem universeReducible_withLowerCandidate_atHigher {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (lowerLevel higherLevel : Nat)
    (belowLower : LevelExpr.denote levelExpr env < lowerLevel)
    (lowerLeHigher : lowerLevel ≤ higherLevel) :
    ReducibleTypeAtDenote env higherLevel
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope)
      (universeDenotePredicate env (denoteBelowFamily env lowerLevel) levelExpr) :=
  have belowHigher : LevelExpr.denote levelExpr env < higherLevel :=
    Nat.lt_of_lt_of_le belowLower lowerLeHigher
  ReducibleTypeStepDenote.ofPointwiseIff
    (ReducibleTypeStepDenote.universeCode levelExpr flag)
    (fun typeCode => universeDenoteCandidate_boundIndependent env levelExpr
      higherLevel lowerLevel belowHigher belowLower typeCode)

end FX1Poly.Typed
