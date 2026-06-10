import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ConvBoolCodeRigidity

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- A closed nat numeral: natZero or natSucc of a numeral. -/
inductive IsNatNumeral {scope : Nat} : RawTerm scope → Prop where
  | zero : IsNatNumeral natZeroCell
  | succ {predecessor : RawTerm scope} :
      IsNatNumeral predecessor → IsNatNumeral (natSuccCell predecessor)

/-- Probe 1: every HasTypeDescNatIntro-typed subject IS a numeral (classifier generalized to dodge the
fixed-index issue; both arms conclude a numeral regardless of classifier). -/
theorem HasTypeDescNatIntro.subjectIsNatNumeral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    IsNatNumeral subject := by
  induction derivation with
  | natZeroIntro => exact IsNatNumeral.zero
  | natSuccIntro _predecessor _predecessorTyped ih => exact IsNatNumeral.succ ih

/-- Probe 2: natTypeCell is a no-step leaf, so it is never Conv a Π-code (mirror of bool). -/
theorem Conv.natTypeCell_not_piTyCode_probe {scope : Nat}
    {piDomain : RawTerm scope} {piCodomain : RawTerm (scope + 1)}
    (convertibility : Conv (natTypeCell : RawTerm scope) (piTyCodeCell piDomain piCodomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) reduct step)
      leftChain
  obtain ⟨_, _, rightCommonEq, _, _⟩ := StepStar.shapeStable_piTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_natCode = Generator.gen_piTyCode)

/-- Probe 3: natTypeCell never Conv a universe code (both no-step leaves). -/
theorem Conv.natTypeCell_not_universeCode_probe {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility : Conv (natTypeCell : RawTerm scope) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) reduct step)
      leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_natCode = Generator.gen_universeCode)

/-- Probe 4: the closed Nat canonicity assembly via the generic grown-rigidity packaging. -/
theorem closedNatCanonicalForms_probe {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ IsNatNumeral value := by
  refine dataCanonicityFromGrownRigidity
    (profile := profile)
    (isValue := fun value => IsNatNumeral value)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescNatIntro profile .empty standaloneSubject natTypeCell)
    (fun standaloneSubject standaloneTyped =>
      ⟨standaloneSubject, StepStar.refl _, standaloneTyped.subjectIsNatNumeral⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.natTypeCell_not_piTyCode_probe convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.natTypeCell_not_universeCode_probe convToUniverseCode)
    subject typed

/-- Probe 5: non-vacuity — natOne (succ 0) is canonical. -/
theorem closedNatCanonicalForms_natOne_probe {profile : PolyProfile} :
    ∃ value : RawTerm 0, StepStar (natSuccCell natZeroCell : RawTerm 0) value ∧ IsNatNumeral value :=
  closedNatCanonicalForms_probe (profile := profile) (Or.inl HasTypeDescNatIntro.natOneTyped)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescNatIntro.subjectIsNatNumeral
#print axioms FX1Poly.Typed.Conv.natTypeCell_not_piTyCode_probe
#print axioms FX1Poly.Typed.Conv.natTypeCell_not_universeCode_probe
#print axioms FX1Poly.Typed.closedNatCanonicalForms_probe
#print axioms FX1Poly.Typed.closedNatCanonicalForms_natOne_probe
