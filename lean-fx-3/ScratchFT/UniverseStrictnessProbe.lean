import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.WfContext

/-! Probe (NEVER committed): universe-formation level-strictness (0-FP soundness corpus).
    The universe rule gives Type@e : Type@(e+1) EXACTLY — a universe code's classifier is Conv to
    Type@(e+1) (inversion, one line via uniqueness), so the engine rejects level over-shoot. -/

namespace FX1Poly.Typed.Spike

open FX1Poly.Core FX1Poly.Universe

-- The inversion: a universe code is classified by EXACTLY its successor level (up to Conv).
theorem universeCodeClassifierConvToSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (typed : HasType profile context (universeCodeCell levelExpr flag) classifier) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.universeFormation context levelExpr flag)

-- Concrete over-shoot rejection: Type@0 is NOT typed at Type@2 (only Type@1).
theorem universeCode_notTypedAtDoubleSuccessor {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag : RawTerm 0)
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
    universeCodeClassifierConvToSuccessor LevelExpr.lzero flag WfContext.emptyIsWellFormed typed
  have levelEq : LevelExpr.lzero.lsucc.lsucc = LevelExpr.lzero.lsucc :=
    (universeCodeCell_inj_of_conv conv).1
  exact absurd levelEq (by decide)

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.universeCodeClassifierConvToSuccessor
#print axioms FX1Poly.Typed.Spike.universeCode_notTypedAtDoubleSuccessor
