import FX1Poly.Core.StrongNormalizationConstructors

namespace FX1Poly.Core

-- 1-child inversion: listCode (copy of from_optionSome)
theorem Step.from_listCode_probe
    {scope : Nat} {elementCode : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_listCode () (.childCons elementCode .childNil)) target) :
    ∃ (elementAfter : RawTerm scope),
      target = .mkGen .gen_listCode () (.childCons elementAfter .childNil) ∧
      Step elementCode elementAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ elementStep =>
          rename_i elementAfter
          exact ⟨elementAfter, rfl, elementStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

-- 1-child inversion: optionCode
theorem Step.from_optionCode_probe
    {scope : Nat} {elementCode : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_optionCode () (.childCons elementCode .childNil)) target) :
    ∃ (elementAfter : RawTerm scope),
      target = .mkGen .gen_optionCode () (.childCons elementAfter .childNil) ∧
      Step elementCode elementAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ elementStep =>
          rename_i elementAfter
          exact ⟨elementAfter, rfl, elementStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

-- 3-child inversion: idCode (typeCode, leftRaw, rightRaw)
theorem Step.from_idCode_probe
    {scope : Nat} {typeCode leftRaw rightRaw : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_idCode ()
              (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil))))
           target) :
    (∃ (typeAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeAfter (.childCons leftRaw (.childCons rightRaw .childNil))) ∧
        Step typeCode typeAfter)
    ∨ (∃ (leftAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeCode (.childCons leftAfter (.childCons rightRaw .childNil))) ∧
        Step leftRaw leftAfter)
    ∨ (∃ (rightAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeCode (.childCons leftRaw (.childCons rightAfter .childNil))) ∧
        Step rightRaw rightAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ typeStep =>
          rename_i typeAfter
          exact Or.inl ⟨typeAfter, rfl, typeStep⟩
      | there _ tailStep1 =>
          cases tailStep1 with
          | here _ leftStep =>
              rename_i leftAfter
              exact Or.inr (Or.inl ⟨leftAfter, rfl, leftStep⟩)
          | there _ tailStep2 =>
              cases tailStep2 with
              | here _ rightStep =>
                  rename_i rightAfter
                  exact Or.inr (Or.inr ⟨rightAfter, rfl, rightStep⟩)
              | there _ restStep =>
                  exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

-- The reusable 3-child congruence SN combinator (extends one/twoChildCong).
theorem isStronglyNormalizing_of_threeChildCong_probe
    {firstScope secondScope thirdScope parentScope : Nat}
    (wrapParent :
      RawTerm firstScope → RawTerm secondScope → RawTerm thirdScope → RawTerm parentScope)
    (invertParentStep :
      ∀ {firstChild : RawTerm firstScope} {secondChild : RawTerm secondScope}
        {thirdChild : RawTerm thirdScope} {targetParent : RawTerm parentScope},
        Step (wrapParent firstChild secondChild thirdChild) targetParent →
          (∃ targetFirst : RawTerm firstScope,
            targetParent = wrapParent targetFirst secondChild thirdChild ∧
              Step firstChild targetFirst)
          ∨ (∃ targetSecond : RawTerm secondScope,
            targetParent = wrapParent firstChild targetSecond thirdChild ∧
              Step secondChild targetSecond)
          ∨ (∃ targetThird : RawTerm thirdScope,
            targetParent = wrapParent firstChild secondChild targetThird ∧
              Step thirdChild targetThird))
    {firstChild : RawTerm firstScope}
    (firstTerminates : IsStronglyNormalizing firstChild)
    {secondChild : RawTerm secondScope}
    (secondTerminates : IsStronglyNormalizing secondChild)
    {thirdChild : RawTerm thirdScope}
    (thirdTerminates : IsStronglyNormalizing thirdChild) :
    IsStronglyNormalizing (wrapParent firstChild secondChild thirdChild) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm secondScope} {currentThird : RawTerm thirdScope},
        IsStronglyNormalizing currentSecond → IsStronglyNormalizing currentThird →
          IsStronglyNormalizing (wrapParent currentFirst currentSecond currentThird))
    (m := fun currentFirst _ firstChildIH => by
      intro currentSecond currentThird currentSecondTerminates currentThirdTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            ∀ {innerThird : RawTerm thirdScope},
              IsStronglyNormalizing innerThird →
                IsStronglyNormalizing (wrapParent currentFirst innerSecond innerThird))
          (m := fun midSecond midSecondSuccessors secondChildIH => by
            intro innerThird innerThirdTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerThird =>
                  IsStronglyNormalizing (wrapParent currentFirst midSecond innerThird))
                (m := fun currentThirdValue currentThirdSuccessors thirdChildIH =>
                  Acc.intro (wrapParent currentFirst midSecond currentThirdValue)
                    (fun targetParent parentStep => by
                      rcases invertParentStep parentStep with
                        ⟨targetFirst, targetEq, firstStep⟩ |
                        ⟨targetSecond, targetEq, secondStep⟩ |
                        ⟨targetThird, targetEq, thirdStep⟩
                      · rw [targetEq]
                        exact firstChildIH targetFirst firstStep
                          (Acc.intro midSecond midSecondSuccessors)
                          (Acc.intro currentThirdValue currentThirdSuccessors)
                      · rw [targetEq]
                        exact secondChildIH targetSecond secondStep
                          (Acc.intro currentThirdValue currentThirdSuccessors)
                      · rw [targetEq]
                        exact thirdChildIH targetThird thirdStep))
                innerThirdTerminates)
          currentSecondTerminates)
        currentThirdTerminates)
    firstTerminates)
    secondTerminates
    thirdTerminates

-- SN: listCode (1-child)
theorem listCode_isStronglyNormalizing_of_element_probe {scope : Nat}
    {elementCode : RawTerm scope}
    (elementTerminates : IsStronglyNormalizing elementCode) :
    IsStronglyNormalizing
      (.mkGen .gen_listCode () (.childCons elementCode .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentElement =>
      (.mkGen .gen_listCode () (.childCons currentElement .childNil) : RawTerm scope))
    (fun parentStep => Step.from_listCode_probe parentStep)
    elementTerminates

-- SN: optionCode (1-child)
theorem optionCode_isStronglyNormalizing_of_element_probe {scope : Nat}
    {elementCode : RawTerm scope}
    (elementTerminates : IsStronglyNormalizing elementCode) :
    IsStronglyNormalizing
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentElement =>
      (.mkGen .gen_optionCode () (.childCons currentElement .childNil) : RawTerm scope))
    (fun parentStep => Step.from_optionCode_probe parentStep)
    elementTerminates

-- SN: idCode (3-child)
theorem idCode_isStronglyNormalizing_of_type_endpoints_probe {scope : Nat}
    {typeCode leftRaw rightRaw : RawTerm scope}
    (typeTerminates : IsStronglyNormalizing typeCode)
    (leftTerminates : IsStronglyNormalizing leftRaw)
    (rightTerminates : IsStronglyNormalizing rightRaw) :
    IsStronglyNormalizing
      (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_threeChildCong_probe
    (firstScope := scope) (secondScope := scope) (thirdScope := scope) (parentScope := scope)
    (fun currentType currentLeft currentRight =>
      (.mkGen .gen_idCode ()
        (.childCons currentType (.childCons currentLeft (.childCons currentRight .childNil))) :
        RawTerm scope))
    (fun parentStep => Step.from_idCode_probe parentStep)
    typeTerminates leftTerminates rightTerminates

end StepStar
end FX1Poly.Core

-- axiom probes
#print axioms FX1Poly.Core.Step.from_idCode_probe
#print axioms FX1Poly.Core.StepStar.isStronglyNormalizing_of_threeChildCong_probe
#print axioms FX1Poly.Core.StepStar.idCode_isStronglyNormalizing_of_type_endpoints_probe
#print axioms FX1Poly.Core.StepStar.listCode_isStronglyNormalizing_of_element_probe
