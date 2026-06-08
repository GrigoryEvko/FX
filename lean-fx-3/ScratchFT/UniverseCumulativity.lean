import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Core.StratifiedReducibleUniverseDecode

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Level-label-irrelevance of universe membership at a fixed fuel (the model is LevelExpr/flag-coarse).
theorem IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant_probe {scope predLevel : Nat}
    {levelExpr levelExpr' : LevelExpr} {flag flag' : UniverseFlag} {typeCode : RawTerm scope} :
    IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode ↔
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr' flag') typeCode :=
  (IsReducibleMemberAt.universeMembership_iff (levelExpr := levelExpr) (flag := flag)).trans
    (IsReducibleMemberAt.universeMembership_iff (levelExpr := levelExpr') (flag := flag')).symm

-- Cumulativity (single level): a member of Type@e is a member of Type@(lsucc e).
theorem IsReducibleMemberAt.universeCumulativity_probe {scope predLevel : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell (LevelExpr.lsucc levelExpr) flag) typeCode :=
  IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant_probe.mp member

-- Cumulativity (all positive levels).
theorem IsReducibleMemberAtAllPositiveLevels.universeCumulativity_probe {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell (LevelExpr.lsucc levelExpr) flag) typeCode :=
  fun level => IsReducibleMemberAt.universeCumulativity_probe (member level)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant_probe
#print axioms FX1Poly.Typed.IsReducibleMemberAt.universeCumulativity_probe
#print axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.universeCumulativity_probe
