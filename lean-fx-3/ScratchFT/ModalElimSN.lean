import FX1Poly.Core.StrongNormalizationConstructors

namespace FX1Poly.Core

-- 1-child cong inversions (modElim/subsume have NO β+ι root rule — congruence-only)
theorem Step.from_modElim_probe
    {scope : Nat} {modalTerm : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_modElim () (.childCons modalTerm .childNil)) target) :
    ∃ (modalAfter : RawTerm scope),
      target = .mkGen .gen_modElim () (.childCons modalAfter .childNil) ∧
      Step modalTerm modalAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ modalStep =>
          rename_i modalAfter
          exact ⟨modalAfter, rfl, modalStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

theorem Step.from_subsume_probe
    {scope : Nat} {subsumedTerm : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil)) target) :
    ∃ (subsumedAfter : RawTerm scope),
      target = .mkGen .gen_subsume () (.childCons subsumedAfter .childNil) ∧
      Step subsumedTerm subsumedAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ subsumedStep =>
          rename_i subsumedAfter
          exact ⟨subsumedAfter, rfl, subsumedStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

theorem modElim_isStronglyNormalizing_of_child_probe {scope : Nat}
    {modalTerm : RawTerm scope}
    (modalTerminates : IsStronglyNormalizing modalTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentModal =>
      (.mkGen .gen_modElim () (.childCons currentModal .childNil) : RawTerm scope))
    (fun parentStep => Step.from_modElim_probe parentStep)
    modalTerminates

theorem subsume_isStronglyNormalizing_of_child_probe {scope : Nat}
    {subsumedTerm : RawTerm scope}
    (subsumedTerminates : IsStronglyNormalizing subsumedTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentSubsumed =>
      (.mkGen .gen_subsume () (.childCons currentSubsumed .childNil) : RawTerm scope))
    (fun parentStep => Step.from_subsume_probe parentStep)
    subsumedTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.Step.from_modElim_probe
#print axioms FX1Poly.Core.Step.from_subsume_probe
#print axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_of_child_probe
#print axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_of_child_probe
