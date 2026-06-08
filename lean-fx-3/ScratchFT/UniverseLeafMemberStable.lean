import FX1Poly.Typed.DenoteKeyedUniverseDomainPi

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- Member-stability for the universe LEAF above the bound: a reducible member (a type) of Type@levelExpr
at one level above denote levelExpr env is reducible at every level above it -- the fixed decode-set
candidate (universeMembership_levelIrrelevant) is the same at both levels; determinism reconciles. The
leaf twin of universeDomainPi_memberStableAcrossDenoteLevels. -/
theorem universeLeafMemberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {typeMember : RawTerm scope} {sourceLevel : Nat}
    (sourceLevelAbove : LevelExpr.denote levelExpr env < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeMember)
    {targetLevel : Nat} (targetLevelAbove : LevelExpr.denote levelExpr env < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeMember := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree := ReducibleTypeAtDenote.deterministic sourceReducible
    (universeMembership_levelIrrelevant env sourceLevel levelExpr flag sourceLevelAbove)
  exact ⟨_, universeMembership_levelIrrelevant env targetLevel levelExpr flag targetLevelAbove,
    (candidatesAgree typeMember).mp memberInSource⟩

#print axioms FX1Poly.Typed.universeLeafMemberStableAcrossDenoteLevels
