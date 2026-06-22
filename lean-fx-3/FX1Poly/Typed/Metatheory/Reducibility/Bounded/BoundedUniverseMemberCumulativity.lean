import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedFormerEngine
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedGenFormationPiArm
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedReducibility
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge

/-! # FX1Poly/Typed/BoundedUniverseMemberCumulativity
    — member-level universe cumulativity: lift a universe member from a lower level to a higher one (TYTAB-4 step 4)

`universeReducible_withLowerCandidate_atHigher` (DenoteKeyedUniverseBoundedCumulativity) lifts a universe code's
reducibility AS A TYPE across ambient levels below the bound.  This file is the MEMBER-level twin: a bound-reducible
MEMBER of `Type@lowerLevel` is a bound-reducible member of `Type@higherLevel` whenever
`denote lowerLevel env ≤ denote higherLevel env < bound`.

## Why it is needed (the free-`levels` discharge)

The native `formationFundamental` premise quantifies the level list `levels` FREELY, so a cumulative type-former's
output universe `universeCodeCell (lmaxAll levels) flag` carries an arbitrary `levels` while its component obligations
are typed at the FIRST one or two levels (or, when `levels` is exhausted, the forced `Type@0`).  In every reachable
`levels` shape `denote (lmaxAll [obligationLevels]) env ≤ denote (lmaxAll levels) env`, so the Π/Σ formation member
(`fundamentalCumulative{Pi,Sigma}MemberAtBoundedSucc`, built at the obligation levels) lands at a universe BELOW the
required output universe — this lemma lifts it the rest of the way, decoupling the obligation levels from the free
output level.

## The construction

A universe member packages exactly `(denote lowerLevel env < bound) ∧ SN term ∧ reducible-as-type-at-lowerLevel`
(the `universeMembershipIntroAtBounded` decode-set).  The lift reads off the lower bound from the member's candidate
(`universeCodeReducibleAtBounded_belowBound`), projects SN (`stronglyNormalizing_of_universeMemberAtBounded`) and the
reducible-as-type at the lower level (`universeMemberReducibleAsTypeAtDecodedLevelBounded`), lifts that to the higher
level by free bounded cumulativity (`isReducibleBounded_cumulative`), and re-introduces the member at the higher level
(`universeMembershipIntroAtBounded`) with the supplied `higherBelowBound`.  SN is level-independent; only the
reducible-as-type leg moves, exactly as the type-level cumulativity does.

## Zero-axiom verification

Four shipped bounded-universe lemma applications + one `obtain` for the lower bound.  No induction, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-level universe cumulativity (bound-carrying).**  A bound-reducible member of `Type@lowerLevel` is a
bound-reducible member of `Type@higherLevel` whenever `denote lowerLevel env ≤ denote higherLevel env` and
`denote higherLevel env < bound`.  The member's own lower-level bound is read off its candidate; SN transfers
unchanged (level-independent) and the reducible-as-type leg lifts by free bounded cumulativity.  The decoupler that
lets the cumulative Π/Σ formation members (built at the component obligation levels) reach the free output universe
`Type@(lmaxAll levels)` of the native `formationFundamental` premise. -/
theorem universeMemberCumulativeAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (lowerLevel higherLevel : LevelExpr) (flag : UniverseFlag) (term : RawTerm scope)
    (member : IsReducibleMemberAtBounded env bound (universeCodeCell lowerLevel flag) term)
    (lowerLeHigher : LevelExpr.denote lowerLevel env ≤ LevelExpr.denote higherLevel env)
    (higherBelowBound : LevelExpr.denote higherLevel env < bound) :
    IsReducibleMemberAtBounded env bound (universeCodeCell higherLevel flag) term := by
  have lowerBelowBound : LevelExpr.denote lowerLevel env < bound := by
    obtain ⟨_candidate, candidateReducible, _termInCandidate⟩ := member
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have termSN : IsStronglyNormalizing term :=
    stronglyNormalizing_of_universeMemberAtBounded env bound lowerLevel flag term lowerBelowBound member
  have termReducibleAtLower :
      IsReducibleTypeAtBounded env (LevelExpr.denote lowerLevel env) term :=
    universeMemberReducibleAsTypeAtDecodedLevelBounded member lowerBelowBound
  have termReducibleAtHigher :
      IsReducibleTypeAtBounded env (LevelExpr.denote higherLevel env) term :=
    isReducibleBounded_cumulative termReducibleAtLower lowerLeHigher
  exact universeMembershipIntroAtBounded env higherLevel flag bound term higherBelowBound termSN
    termReducibleAtHigher

end FX1Poly.Typed
