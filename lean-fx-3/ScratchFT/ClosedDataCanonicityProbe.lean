import FX1Poly.Typed.OptionCanonicalForms
import FX1Poly.Typed.ListCanonicalForms
import FX1Poly.Typed.ProductEitherCanonicalForms
import FX1Poly.Typed.GrownRigidityCanonicity

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Option: arbitrary-subject canonicity via the generic engine. -/
theorem closedOptionCanonicalForms_probe {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = optionNoneCell ∨ ∃ inner : RawTerm 0, value = optionSomeCell inner) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value => value = optionNoneCell ∨ ∃ inner, value = optionSomeCell inner)
    (StandaloneTyped := fun s => HasTypeDescOptionIntro profile .empty s (optionTypeCell elementType))
    (fun s sTyped => ⟨s, StepStar.refl _, sTyped.subjectIsOptionConstructor⟩)
    (fun _d _c conv => Conv.optionCode_not_piTyCode conv)
    (fun _l _f conv => Conv.optionCode_not_universeCode conv)
    subject typed

/-- List: arbitrary-subject canonicity. -/
theorem closedListCanonicalForms_probe {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed :
      HasTypeDescListIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = listNilCell ∨ ∃ (headValue tailList : RawTerm 0), value = listConsCell headValue tailList) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value =>
      value = listNilCell ∨ ∃ (headValue tailList : RawTerm 0), value = listConsCell headValue tailList)
    (StandaloneTyped := fun s => HasTypeDescListIntro profile .empty s (listTypeCell elementType))
    (fun s sTyped => ⟨s, StepStar.refl _, sTyped.subjectIsListConstructor⟩)
    (fun _d _c conv => Conv.listCode_not_piTyCode conv)
    (fun _l _f conv => Conv.listCode_not_universeCode conv)
    subject typed

/-- Product (Σ-pair): arbitrary-subject canonicity (the rigidities need `.sym` for the Π direction). -/
theorem closedProductCanonicalForms_probe {profile : PolyProfile} {subject : RawTerm 0}
    {firstType secondType : RawTerm 0}
    (typed :
      HasTypeDescPairIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (productTypeCell firstType secondType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (productTypeCell firstType secondType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      ∃ (firstValue secondValue : RawTerm 0), value = pairCell firstValue secondValue :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value => ∃ (firstValue secondValue : RawTerm 0), value = pairCell firstValue secondValue)
    (StandaloneTyped := fun s =>
      HasTypeDescPairIntro profile .empty s (productTypeCell firstType secondType))
    (fun s sTyped => ⟨s, StepStar.refl _, sTyped.subjectIsPair⟩)
    (fun _d _c conv => Conv.piTyCode_not_conv_productCode conv.sym)
    (fun _l _f conv => Conv.productCode_not_universeCode conv)
    subject typed

/-- Either (coproduct = Sum): arbitrary-subject canonicity. -/
theorem closedEitherCanonicalForms_probe {profile : PolyProfile} {subject : RawTerm 0}
    {leftType rightType : RawTerm 0}
    (typed :
      HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (eitherTypeCell leftType rightType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (eitherTypeCell leftType rightType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      ((∃ inner : RawTerm 0, value = eitherInlCell inner) ∨
       (∃ inner : RawTerm 0, value = eitherInrCell inner)) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value =>
      (∃ inner : RawTerm 0, value = eitherInlCell inner) ∨ (∃ inner : RawTerm 0, value = eitherInrCell inner))
    (StandaloneTyped := fun s =>
      HasTypeDescEitherIntro profile .empty s (eitherTypeCell leftType rightType))
    (fun s sTyped => ⟨s, StepStar.refl _, sTyped.subjectIsEitherInjection⟩)
    (fun _d _c conv => Conv.piTyCode_not_conv_eitherCode conv.sym)
    (fun _l _f conv => Conv.eitherCode_not_universeCode conv)
    subject typed

end FX1Poly.Typed

#print axioms FX1Poly.Typed.closedOptionCanonicalForms_probe
#print axioms FX1Poly.Typed.closedListCanonicalForms_probe
#print axioms FX1Poly.Typed.closedProductCanonicalForms_probe
#print axioms FX1Poly.Typed.closedEitherCanonicalForms_probe
