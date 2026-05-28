import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationLeaves
import LeanFX2.Foundation.PolyCell.Core.StepInversion

/-! # Foundation/PolyCell/Core/StrongNormalizationConstructors
    - structural SN closure for congruence-only constructors

This continues the M9/M10 strong-normalization lane after the zero-child
leaf endpoints.  The theorems here cover one-child constructors whose only
current outgoing `Step` is congruence through that child.  Existing
`Step.from_*` inversion lemmas provide the required no-root-reduction evidence.

This is still not global SN, not a reducibility predicate, and not the
fundamental theorem.  It is the first reusable accessibility-closure pattern
needed before scaling to broader certified total terms.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace StepStar

/-- If every parent step is exactly a step in one child, accessibility of that
child lifts to accessibility of the wrapped parent. -/
theorem isStronglyNormalizing_of_oneChildCong
    {childScope parentScope : Nat}
    (wrapParent : RawTerm childScope → RawTerm parentScope)
    (invertParentStep :
      ∀ {sourceChild : RawTerm childScope} {targetParent : RawTerm parentScope},
        Step (wrapParent sourceChild) targetParent →
          ∃ targetChild : RawTerm childScope,
            targetParent = wrapParent targetChild ∧
              Step sourceChild targetChild)
    {sourceChild : RawTerm childScope}
    (childTerminates : IsStronglyNormalizing sourceChild) :
    IsStronglyNormalizing (wrapParent sourceChild) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentChild =>
      IsStronglyNormalizing (wrapParent currentChild))
    (m := fun currentChild _ currentChildIH =>
      Acc.intro (wrapParent currentChild)
        (fun targetParent parentStep => by
          obtain ⟨targetChild, targetEq, childStep⟩ :=
            invertParentStep parentStep
          rw [targetEq]
          exact currentChildIH targetChild childStep))
    childTerminates

/-- Lambda abstraction is strongly normalizing when its body is strongly
normalizing.  The body lives under one fresh binder, but the one-child closure
lemma is scope-polymorphic, so no special binder transport is needed. -/
theorem lam_isStronglyNormalizing_of_body {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyTerminates : IsStronglyNormalizing body) :
    IsStronglyNormalizing
      (.mkGen .gen_lam () (.childCons body .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope + 1)
    (parentScope := scope)
    (fun currentBody =>
      (.mkGen .gen_lam () (.childCons currentBody .childNil) :
        RawTerm scope))
    (fun parentStep => Step.from_lam parentStep)
    bodyTerminates

/-- Natural successor is strongly normalizing when its predecessor is strongly
normalizing. -/
theorem natSucc_isStronglyNormalizing_of_predecessor {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorTerminates : IsStronglyNormalizing predecessor) :
    IsStronglyNormalizing
      (.mkGen .gen_natSucc () (.childCons predecessor .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentPredecessor =>
      (.mkGen .gen_natSucc ()
        (.childCons currentPredecessor .childNil) : RawTerm scope))
    (fun parentStep => Step.from_natSucc parentStep)
    predecessorTerminates

/-- Option `some` is strongly normalizing when its payload is strongly
normalizing. -/
theorem optionSome_isStronglyNormalizing_of_value {scope : Nat}
    {value : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value) :
    IsStronglyNormalizing
      (.mkGen .gen_optionSome () (.childCons value .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentValue =>
      (.mkGen .gen_optionSome ()
        (.childCons currentValue .childNil) : RawTerm scope))
    (fun parentStep => Step.from_optionSome parentStep)
    valueTerminates

/-- Either-left injection is strongly normalizing when its payload is strongly
normalizing. -/
theorem eitherInl_isStronglyNormalizing_of_value {scope : Nat}
    {value : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherInl () (.childCons value .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentValue =>
      (.mkGen .gen_eitherInl ()
        (.childCons currentValue .childNil) : RawTerm scope))
    (fun parentStep => Step.from_eitherInl parentStep)
    valueTerminates

/-- Either-right injection is strongly normalizing when its payload is strongly
normalizing. -/
theorem eitherInr_isStronglyNormalizing_of_value {scope : Nat}
    {value : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherInr () (.childCons value .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentValue =>
      (.mkGen .gen_eitherInr ()
        (.childCons currentValue .childNil) : RawTerm scope))
    (fun parentStep => Step.from_eitherInr parentStep)
    valueTerminates

/-- Reflexivity witnesses are strongly normalizing when their raw witness is
strongly normalizing. -/
theorem refl_isStronglyNormalizing_of_witness {scope : Nat}
    {rawWitness : RawTerm scope}
    (witnessTerminates : IsStronglyNormalizing rawWitness) :
    IsStronglyNormalizing
      (.mkGen .gen_refl () (.childCons rawWitness .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentWitness =>
      (.mkGen .gen_refl ()
        (.childCons currentWitness .childNil) : RawTerm scope))
    (fun parentStep => Step.from_refl parentStep)
    witnessTerminates

end StepStar
end LeanFX2.Foundation.PolyCell.Core
