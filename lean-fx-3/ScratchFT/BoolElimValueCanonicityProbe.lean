import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.CombinedBoolCanonicalForms

/-! Probe: the FIRST genuinely-NON-VACUOUS eliminator-computing canonicity. A standalone bool eliminator with
    DATA-VALUE branches (boolElim b true false : Bool — which the current grown-branch engine CANNOT type), whose
    closed instances COMPUTE by ι to a bool value. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The bool eliminator INTO Bool: branches are data-intro values at boolCode (so `boolElim b true false : Bool`
is typeable). Standalone (NOT mutual, NOT an arm of any engine), the data-value-branch twin of HasTypeDescBoolElim
(whose branches are grown-typed). The non-dependent eliminator with a constant Bool motive. -/
inductive HasTypeDescBoolElimValue (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | boolElimValueIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee thenBranch elseBranch : RawTerm scope)
      (scrutineeTyped : HasTypeDescDataIntro profile context scrutinee boolTypeCell)
      (thenTyped : HasTypeDescDataIntro profile context thenBranch boolTypeCell)
      (elseTyped : HasTypeDescDataIntro profile context elseBranch boolTypeCell) :
      HasTypeDescBoolElimValue profile context
        (boolElimCell scrutinee thenBranch elseBranch) boolTypeCell

/-- Non-vacuous typing smoke: `boolElim(boolTrue, boolTrue, boolFalse) : Bool`. -/
theorem HasTypeDescBoolElimValue.smokeProbe {profile : PolyProfile} :
    HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      (boolElimCell boolTrueCell boolTrueCell boolFalseCell) boolTypeCell :=
  HasTypeDescBoolElimValue.boolElimValueIntro TypingContext.empty boolTrueCell boolTrueCell boolFalseCell
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescDataIntro.boolFalseTyped TypingContext.empty)

/-- ★ NON-VACUOUS eliminator-computing canonicity: a closed `boolElim b t e : Bool` (data-value branches)
COMPUTES by a single ι-step to a bool VALUE. The scrutinee is boolTrue/boolFalse, so the eliminator FIRES to the
selected branch, which is itself a bool value. The FIRST eliminator-computing canonicity where the eliminator
genuinely computes (not a vacuity). -/
theorem boolElimValueCanonicityProbe {profile : PolyProfile} {subject : RawTerm 0}
    (derivation : HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell) := by
  cases derivation with
  | boolElimValueIntro scrutinee thenBranch elseBranch scrutineeTyped thenTyped elseTyped =>
      rcases standaloneBoolCanonicalForms (Or.inl scrutineeTyped) with scrutEq | scrutEq
      · subst scrutEq
        rcases standaloneBoolCanonicalForms (Or.inl thenTyped) with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single Step.iotaBoolTrue, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single Step.iotaBoolTrue, Or.inr rfl⟩
      · subst scrutEq
        rcases standaloneBoolCanonicalForms (Or.inl elseTyped) with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single Step.iotaBoolFalse, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single Step.iotaBoolFalse, Or.inr rfl⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescBoolElimValue.smokeProbe
#print axioms FX1Poly.Typed.boolElimValueCanonicityProbe
