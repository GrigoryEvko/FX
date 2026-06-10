import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.CombinedBoolCanonicalForms

/-! Probe: the bool ELIMINATOR engine contributes a VACUOUS disjunct to closed-normal canonical forms — a closed
    NORMAL term typed by HasTypeDescBoolElim is impossible (the scrutinee is a closed DataIntro value, so the
    eliminator ι-fires → not normal). First concrete piece of #1138 (eliminator-computing canonicity). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A closed NORMAL term typed by the bool eliminator engine is impossible: the scrutinee is typed by the
data-intro engine at boolCode, hence is boolTrue/boolFalse (standaloneBoolCanonicalForms), so the boolElim is an
ι-redex (Step.iotaBoolTrue/iotaBoolFalse) — `cases normal` refutes since the NF checker computes false on the
head redex. -/
theorem HasTypeDescBoolElim.noClosedNormalBoolElimProbe {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0)
      subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  cases derivation with
  | boolElimIntro scrutinee thenBranch elseBranch _resultType scrutineeTyped
      _thenTyped _elseTyped =>
      rcases standaloneBoolCanonicalForms (Or.inl scrutineeTyped) with scrutineeEq | scrutineeEq
      · subst scrutineeEq; cases normal
      · subst scrutineeEq; cases normal

/-- The 4-engine combined closed-normal canonical forms: extends closedNormalBoolCanonicalForms (#1064, 3
engines) with the eliminator engine as a VACUOUS disjunct. -/
theorem closedNormalBoolCanonicalFormsWithElimProbe {profile : PolyProfile} {subject : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped | elimTyped
  · exact standaloneBoolCanonicalForms (Or.inl dataIntroTyped)
  · exact standaloneBoolCanonicalForms (Or.inr baseTypeTyped)
  · exact (HasTypeDescPi.noClosedNormalTermAtBoolType grownTyped normal).elim
  · exact (HasTypeDescBoolElim.noClosedNormalBoolElimProbe elimTyped normal).elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescBoolElim.noClosedNormalBoolElimProbe
#print axioms FX1Poly.Typed.closedNormalBoolCanonicalFormsWithElimProbe
