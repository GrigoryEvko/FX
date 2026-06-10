import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Typed.HasTypeDescBoolElim

/-! Probe: genuinely-non-vacuous eliminator-computing bool canonicity at the TYPED layer, stated over the
    component typings (scrutinee 3-engine-typed at boolType, branches data-VALUE-typed at boolType) — the
    deferred follow-on, without needing a combined intro/elim typing judgment. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem closedBoolElimComputesToValue {profile : PolyProfile}
    {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeTyped :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell)
    (thenTyped : HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0)
      thenBranch boolTypeCell)
    (elseTyped : HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0)
      elseBranch boolTypeCell) :
    ∃ value : RawTerm 0, StepStar (boolElimCell scrutinee thenBranch elseBranch) value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsBool⟩ := closedBoolCanonicalForms scrutineeTyped
  cases scrutIsBool with
  | inl scrutIsTrue =>
      subst scrutIsTrue
      exact ⟨thenBranch,
        StepStar.transLast (StepStar.boolElimScrutinee scrutReduces) Step.iotaBoolTrue,
        standaloneBoolCanonicalForms (Or.inl thenTyped)⟩
  | inr scrutIsFalse =>
      subst scrutIsFalse
      exact ⟨elseBranch,
        StepStar.transLast (StepStar.boolElimScrutinee scrutReduces) Step.iotaBoolFalse,
        standaloneBoolCanonicalForms (Or.inl elseTyped)⟩

#print axioms closedBoolElimComputesToValue

end FX1Poly.Typed
