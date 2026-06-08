import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.UniverseCodeConversion

/-! Scratch (SN-43 totalBridge): the conv-arm assembly. The motive's conjunct-2 guard must be CONVERTIBILITY
(`Conv classifier (Type@e f)`), not syntactic equality, so it survives through conv via `Conv.trans`. The leaf
universeFormation arm now consumes `universeCodeCell_inj_of_conv`. The non-variable conv arm is fully clean:
conjunct-1 via `convWithLevelFlexibleReclassifier` (reclassifier flexibility from its conjunct-2 at Conv.refl),
conjunct-2 via `Conv.trans` + the subject's conjunct-2. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe motive: convertibility-guarded conjunct-2. -/
def RBCConv (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
    Conv classifier (universeCodeCell levelExpr flag) →
    (∀ index : Fin scope, subject ≠ variableCell index) →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

theorem RBCConv.var {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    RBCConv profile contextLevels context (variableCell index) (context.lookup index) :=
  ⟨⟨contextLevels index, ValidTyping.var contextLevels context index⟩,
   fun _levelExpr _flag _classifierConv subjectNotVariable => absurd rfl (subjectNotVariable index)⟩

theorem RBCConv.universeFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RBCConv profile contextLevels context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨⟨0 + 1, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩,
   fun _outLevel _outFlag classifierConv _subjectNotVariable => by
     obtain ⟨rfl, rfl⟩ := universeCodeCell_inj_of_conv classifierConv
     exact universeFormation_isLevelFlexible contextLevels context levelExpr flag⟩

theorem RBCConv.convNonVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectIH : RBCConv profile contextLevels context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierIH : RBCConv profile contextLevels context reclassifier (universeCodeCell levelExpr flag))
    (reclassifierNotVariable : ∀ index : Fin scope, reclassifier ≠ variableCell index) :
    RBCConv profile contextLevels context subject reclassifier := by
  obtain ⟨⟨subjectLevel, subjectValid⟩, subjectFlexible⟩ := subjectIH
  refine ⟨?_, ?_⟩
  · have reclassifierFlexible :=
      reclassifierIH.2 levelExpr flag (Conv.refl _) reclassifierNotVariable
    exact ValidTyping.convWithLevelFlexibleReclassifier contextLevels subjectLevel subjectValid converts
      reclassifierFlexible
  · intro outLevel outFlag reclassifierConvUniverse subjectNotVariable
    exact subjectFlexible outLevel outFlag (Conv.trans converts reclassifierConvUniverse) subjectNotVariable

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RBCConv.var
#print axioms FX1Poly.Typed.RBCConv.universeFormation
#print axioms FX1Poly.Typed.RBCConv.convNonVariableReclassifier
