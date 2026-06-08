import FX1Poly.Typed.UniverseFormationStrictness

/-! SCRATCH: general (all-level, all-WfContext) no-Type-in-Type + no-inflation — SN-140 L1. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- THE headline Girard-paradox precursor, at ALL levels and ALL well-formed contexts.
theorem universeCode_notTypedAtSelf_general_probe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor levelExpr flag contextWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr)

-- no level inflation, general: Type@e is NOT typed at Type@(e+2).
theorem universeCode_notTypedAboveSuccessor_general_probe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr.lsucc.lsucc flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor levelExpr flag contextWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr.lsucc).symm

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeCode_notTypedAtSelf_general_probe
#print axioms FX1Poly.Typed.universeCode_notTypedAboveSuccessor_general_probe
