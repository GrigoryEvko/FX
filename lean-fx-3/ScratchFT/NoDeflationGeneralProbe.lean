import FX1Poly.Typed.UniverseFormationStrictness

/-! SCRATCH: general no-deflation — needs e ≠ e.lsucc.lsucc (mirrors ne_lsucc_self). -/

namespace FX1Poly.Universe

-- The double-successor predicativity guard: e ≠ e + 2.  Same structural induction as ne_lsucc_self.
theorem LevelExpr.ne_lsuccLsucc_self_probe (levelExpr : LevelExpr) :
    levelExpr ≠ LevelExpr.lsucc (LevelExpr.lsucc levelExpr) := by
  induction levelExpr with
  | lzero => intro selfEq; cases selfEq
  | lsucc inner ih =>
      intro selfEq
      injection selfEq with innerEq
      exact ih innerEq
  | lmax left right _ _ => intro selfEq; cases selfEq
  | limax left right _ _ => intro selfEq; cases selfEq
  | lvar index => intro selfEq; cases selfEq

end FX1Poly.Universe

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- no level deflation, general: Type@(e+1) is NOT typed at Type@e.
theorem universeCode_notTypedBelowSuccessor_general_probe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr.lsucc flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor levelExpr.lsucc flag contextWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsuccLsucc_self_probe levelExpr)

end FX1Poly.Typed

#print axioms FX1Poly.Universe.LevelExpr.ne_lsuccLsucc_self_probe
#print axioms FX1Poly.Typed.universeCode_notTypedBelowSuccessor_general_probe
