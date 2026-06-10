import FX1Poly.Typed.BoolElimClosedNormalForms
import FX1Poly.Typed.ClosedBoolCanonicity

/-! Probe: ARBITRARY-subject 4-engine bool canonicity. The bool-elim engine's branches are GROWN-typed; the grown
    engine has no closed inhabitant of boolTypeCell (noClosedGrownTermAtBoolType), so a closed boolElim AT
    boolTypeCell is impossible by inverting to a branch — no SN/SR. Upgrades the closed-NORMAL 4-engine forms. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A closed bool-elim term AT boolTypeCell is impossible (ARBITRARY subject): inverting the derivation gives a
branch grown-typed at boolTypeCell, which is vacuous (noClosedGrownTermAtBoolType). The current bool-elim engine
has GROWN branches, so it cannot eliminate INTO a data type — vacuous at boolCode. -/
theorem HasTypeDescBoolElim.noClosedBoolElimAtBoolTypeProbe {profile : PolyProfile} {subject : RawTerm 0}
    (derivation : HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell) :
    False := by
  cases derivation with
  | boolElimIntro scrutinee thenBranch elseBranch resultType _scrutineeTyped thenTyped _elseTyped =>
      exact HasTypeDescPi.noClosedGrownTermAtBoolType thenTyped

/-- ARBITRARY-subject 4-engine bool canonicity: a closed term typed at boolTypeCell by ANY of the four engines
reduces to boolTrue/boolFalse. Upgrades closedNormalBoolCanonicalFormsWithElim (closed-normal) off the normal
hypothesis — the eliminator disjunct is now ruled out for ARBITRARY subjects (the branch grown-vacuity, no SN/SR). -/
theorem closedBoolCanonicalFormsWithElimProbe {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped | elimTyped
  · rcases standaloneBoolCanonicalForms (Or.inl dataIntroTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · rcases standaloneBoolCanonicalForms (Or.inr baseTypeTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · exact (HasTypeDescPi.noClosedGrownTermAtBoolType grownTyped).elim
  · exact (HasTypeDescBoolElim.noClosedBoolElimAtBoolTypeProbe elimTyped).elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescBoolElim.noClosedBoolElimAtBoolTypeProbe
#print axioms FX1Poly.Typed.closedBoolCanonicalFormsWithElimProbe
