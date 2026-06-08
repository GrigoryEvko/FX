import FX1Poly.Typed.ValidTypingRefinedMotive

/-! Scratch (SN-43 totalBridge, step 3-4): the REVISED bridge motive that fixes the var-arm wall.

`RefinedTotalBridgeConclusion`'s conjunct-2 demanded `IsLevelFlexibleTypeCode` for EVERY universe-classified
subject — unsatisfiable for a TYPE VARIABLE (`var j : Type@e`, pinned to `contextLevels j`). The fix: add the
guard `(∀ index, subject ≠ variableCell index)` to conjunct-2, EXCLUDING variable subjects from the flexibility
demand. Then:
  - the `var` arm discharges conjunct-2 VACUOUSLY (the subject IS `variableCell index`, so the guard
    `∀ j, variableCell index ≠ variableCell j` is false at `j := index`);
  - the `universeFormation` arm (subject a universe code, NOT a variable) produces flexibility via the shipped
    `universeFormation_isLevelFlexible`.
This file probes the motive + its two clean leaf arms. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- The revised total-bridge conclusion: single-level validity, plus level-flexibility for a universe-classified
subject that is NOT a variable.  The variable exclusion is the var-arm fix. -/
def RevisedBridgeConclusion (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag), classifier = universeCodeCell levelExpr flag →
    (∀ index : Fin scope, subject ≠ variableCell index) →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

/-- The var arm of the revised motive: conjunct-1 by `ValidTyping.var`, conjunct-2 vacuous (subject is a
variable, so the non-variable guard is contradictory). -/
theorem RevisedBridgeConclusion.var {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    RevisedBridgeConclusion profile contextLevels context
      (variableCell index) (context.lookup index) :=
  ⟨⟨contextLevels index, ValidTyping.var contextLevels context index⟩,
   fun _levelExpr _flag _classifierEq subjectNotVariable =>
     absurd rfl (subjectNotVariable index)⟩

/-- The universeFormation arm of the revised motive: conjunct-1 by `ValidTyping.universeFormation`, conjunct-2
by `universeFormation_isLevelFlexible` (a universe code is not a variable, so the guard is met). -/
theorem RevisedBridgeConclusion.universeFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RevisedBridgeConclusion profile contextLevels context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨⟨0 + 1, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩,
   fun _levelExpr _flag classifierEq _subjectNotVariable => by
     obtain ⟨rfl, rfl⟩ := universeCodeCell_inj classifierEq
     exact universeFormation_isLevelFlexible contextLevels context levelExpr flag⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RevisedBridgeConclusion.var
#print axioms FX1Poly.Typed.RevisedBridgeConclusion.universeFormation
