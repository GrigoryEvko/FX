import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedUniverseMemberCumulativity
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDomainInhabitant
import FX1Poly.Typed.Engine.Formation.FormerOutputLevelBounds

/-! # FX1Poly/Typed/CumulativeFreeLevelsSupport
    — `lmaxFold` denote-monotonicity + the classifier-lift wrapper for the free-`levels` cumulative arm (TYTAB-4)

The native `formationFundamental` premise quantifies the level list FREELY, while the cumulative formation members
(`fundamentalCumulative{Pi,Sigma}MemberAtBoundedSucc`) are built at the component OBLIGATION levels (the first one or
two of `levels`, or the forced `Type@0` when `levels` is short).  Bridging the obligation-level member to the free
output universe `Type@(lmaxAll levels)` needs two arithmetic facts about the iterated `lmax` fold plus the
member-level universe cumulativity lift — packaged here so the per-generator cumulative arms stay short.

## The declarations

  * `denote_le_lmaxFold` — the fold is monotone in its accumulator: `denote accumulator env ≤ denote (lmaxFold
    accumulator rest) env`.  Each fold step only joins in more levels, never lowers the running max.  Gives the
    `lower ≤ higher` premise of the lift when `levels` has surplus tail elements beyond the obligation levels.
  * `denote_lmaxFold_lt` — the fold stays below the bound: if the accumulator and every tail level denote below
    `bound`, so does the whole fold.  Gives the `higher < bound` premise of the lift from the per-level gate.
  * `fundamentalConclusion_universeCumulative` — the classifier-lift wrapper: a `FundamentalConclusionAtBoundedSucc`
    at `Type@lowerLevel` is one at `Type@higherLevel` whenever `denote lowerLevel env ≤ denote higherLevel env <
    bound`, lifting the member per-substitution via `universeMemberCumulativeAtBounded`.

## Zero-axiom verification

Two structural `List` inductions (mirroring `lmaxFold`'s two clauses) over the shipped `levelMax_le_left` /
`levelMax_lt` + `denote_lmax`; the wrapper is one `intro` then the member cumulativity under `subst_universeCodeCell`.
No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `lmaxFold` is monotone in its accumulator.**  `denote accumulator env ≤ denote (lmaxFold accumulator rest)
env`: each fold step replaces the accumulator by `lmax accumulator headLevel ≥ accumulator`, so folding in more
levels never lowers the running max.  Supplies the `lower ≤ higher` premise of the universe-member lift when the
free `levels` carries surplus tail elements beyond the obligation levels. -/
theorem denote_le_lmaxFold (env : Nat → Nat) :
    ∀ (rest : List LevelExpr) (accumulator : LevelExpr),
      LevelExpr.denote accumulator env ≤ LevelExpr.denote (lmaxFold accumulator rest) env
  | [], _accumulator => Nat.le_refl _
  | headLevel :: restLevels, accumulator => by
      have accumulatorLeStep :
          LevelExpr.denote accumulator env
            ≤ LevelExpr.denote (LevelExpr.lmax accumulator headLevel) env := by
        rw [LevelExpr.denote_lmax]
        exact levelMax_le_left _ _
      exact Nat.le_trans accumulatorLeStep
        (denote_le_lmaxFold env restLevels (LevelExpr.lmax accumulator headLevel))

/-- **The `lmaxFold` stays below the bound.**  If the accumulator and every tail level denote strictly below
`bound`, so does the whole fold: each step joins two below-bound levels (`levelMax_lt`), staying below.  Supplies the
`higher < bound` premise of the universe-member lift from the per-level gate. -/
theorem denote_lmaxFold_lt (env : Nat → Nat) (bound : Nat) :
    ∀ (rest : List LevelExpr) (accumulator : LevelExpr),
      LevelExpr.denote accumulator env < bound →
      (∀ levelExpr, levelExpr ∈ rest → LevelExpr.denote levelExpr env < bound) →
      LevelExpr.denote (lmaxFold accumulator rest) env < bound
  | [], _accumulator, accumulatorBelowBound, _restBelowBound => accumulatorBelowBound
  | headLevel :: restLevels, accumulator, accumulatorBelowBound, restBelowBound => by
      have headBelowBound : LevelExpr.denote headLevel env < bound :=
        restBelowBound headLevel (List.Mem.head _)
      have stepBelowBound :
          LevelExpr.denote (LevelExpr.lmax accumulator headLevel) env < bound := by
        rw [LevelExpr.denote_lmax]
        exact levelMax_lt accumulatorBelowBound headBelowBound
      exact denote_lmaxFold_lt env bound restLevels (LevelExpr.lmax accumulator headLevel)
        stepBelowBound (fun levelExpr levelMem => restBelowBound levelExpr (List.Mem.tail _ levelMem))

/-- **The classifier-lift wrapper.**  A `FundamentalConclusionAtBoundedSucc` member of `Type@lowerLevel` is a member
of `Type@higherLevel` whenever `denote lowerLevel env ≤ denote higherLevel env` and `denote higherLevel env < bound`:
under any closing substitution the universe codes are substitution-inert, so the per-substitution member lifts by
`universeMemberCumulativeAtBounded`.  Raises a cumulative formation member from the component obligation universe to
the free output universe `Type@(lmaxAll levels)`. -/
theorem fundamentalConclusion_universeCumulative {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope) {subject : RawTerm scope}
    (lowerLevel higherLevel : LevelExpr) (flag : UniverseFlag)
    (member : FundamentalConclusionAtBoundedSucc env bound context subject
      (universeCodeCell lowerLevel flag))
    (lowerLeHigher : LevelExpr.denote lowerLevel env ≤ LevelExpr.denote higherLevel env)
    (higherBelowBound : LevelExpr.denote higherLevel env < bound) :
    FundamentalConclusionAtBoundedSucc env bound context subject
      (universeCodeCell higherLevel flag) := by
  intro _targetScope substitution envReducible
  have substitutedMember := member substitution envReducible
  rw [subst_universeCodeCell] at substitutedMember ⊢
  exact universeMemberCumulativeAtBounded env bound lowerLevel higherLevel flag
    (RawTerm.subst substitution subject) substitutedMember lowerLeHigher higherBelowBound

end FX1Poly.Typed
