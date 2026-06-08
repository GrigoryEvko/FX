import FX1Poly.Typed.DenoteKeyedReducibility

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The universe candidate is bound-independent below the bound.** When the universe's decoded level is
strictly below BOTH ambient levels, its denote member candidate (which reaches `lowerAt` only at the fixed
index `denote levelExpr env`) rewrites — via the below-family coherence `denoteBelowFamily_eq_reducible` — to
the bound-independent `ReducibleTypeAtDenote env (denote levelExpr env)` at both levels. This is the positive
resolution, at the CANDIDATE level, of the cumulativity obstruction (DenoteKeyedCumulativityObstruction): the
universe candidate only DRIFTS in the GAP regime (decoded level >= ambient); below the bound it is stable. -/
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

#print axioms FX1Poly.Typed.universeDenoteCandidate_boundIndependent

/-- **Universe cumulativity below the bound (same-candidate transport up).** When `denote levelExpr env <
lowerLevel <= higherLevel`, the universe `Type@levelExpr` is reducible-as-type at the HIGHER level carrying
the LOWER level's member candidate: the universe arm fires at the higher level (with the higher candidate),
then `ofPointwiseIff` swaps to the lower candidate via bound-independence. This is the cumulativity the
obstruction said was missing -- it holds precisely in the BOUNDED regime (universe below ambient), isolating
the genuine obstruction to the gap regime (denote >= ambient) ALONE. -/
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

#print axioms FX1Poly.Typed.universeReducible_withLowerCandidate_atHigher
