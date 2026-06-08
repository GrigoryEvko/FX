import FX1Poly.Core.StrongNormalizationConstructors

namespace FX1Poly.Core

-- 2-child cong inversions (linearArrow/tensorProduct have no β+ι root rule — congruence-only)
theorem Step.from_linearArrow_probe
    {scope : Nat} {source target : RawTerm scope} {reduct : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil))) reduct) :
    (∃ sourceAfter : RawTerm scope,
        reduct = .mkGen .gen_linearArrow () (.childCons sourceAfter (.childCons target .childNil)) ∧
        Step source sourceAfter)
    ∨ (∃ targetAfter : RawTerm scope,
        reduct = .mkGen .gen_linearArrow () (.childCons source (.childCons targetAfter .childNil)) ∧
        Step target targetAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ sourceStep =>
          rename_i sourceAfter
          exact Or.inl ⟨sourceAfter, rfl, sourceStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ targetStep =>
              rename_i targetAfter
              exact Or.inr ⟨targetAfter, rfl, targetStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

theorem Step.from_tensorProduct_probe
    {scope : Nat} {leftFactor rightFactor : RawTerm scope} {reduct : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_tensorProduct () (.childCons leftFactor (.childCons rightFactor .childNil))) reduct) :
    (∃ leftAfter : RawTerm scope,
        reduct = .mkGen .gen_tensorProduct () (.childCons leftAfter (.childCons rightFactor .childNil)) ∧
        Step leftFactor leftAfter)
    ∨ (∃ rightAfter : RawTerm scope,
        reduct = .mkGen .gen_tensorProduct () (.childCons leftFactor (.childCons rightAfter .childNil)) ∧
        Step rightFactor rightAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftStep =>
          rename_i leftAfter
          exact Or.inl ⟨leftAfter, rfl, leftStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightStep =>
              rename_i rightAfter
              exact Or.inr ⟨rightAfter, rfl, rightStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

theorem linearArrow_isStronglyNormalizing_of_source_target_probe {scope : Nat}
    {source target : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing source)
    (targetTerminates : IsStronglyNormalizing target) :
    IsStronglyNormalizing
      (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentSource currentTarget =>
      (.mkGen .gen_linearArrow ()
        (.childCons currentSource (.childCons currentTarget .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_linearArrow_probe parentStep)
    sourceTerminates targetTerminates

theorem tensorProduct_isStronglyNormalizing_of_factors_probe {scope : Nat}
    {leftFactor rightFactor : RawTerm scope}
    (leftTerminates : IsStronglyNormalizing leftFactor)
    (rightTerminates : IsStronglyNormalizing rightFactor) :
    IsStronglyNormalizing
      (.mkGen .gen_tensorProduct ()
        (.childCons leftFactor (.childCons rightFactor .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentLeft currentRight =>
      (.mkGen .gen_tensorProduct ()
        (.childCons currentLeft (.childCons currentRight .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_tensorProduct_probe parentStep)
    leftTerminates rightTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.Step.from_linearArrow_probe
#print axioms FX1Poly.Core.Step.from_tensorProduct_probe
#print axioms FX1Poly.Core.StepStar.linearArrow_isStronglyNormalizing_of_source_target_probe
#print axioms FX1Poly.Core.StepStar.tensorProduct_isStronglyNormalizing_of_factors_probe
