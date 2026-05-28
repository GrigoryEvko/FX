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

/-- If every parent step is exactly a step in one of two children, accessibility
of both children lifts to accessibility of the wrapped parent. -/
theorem isStronglyNormalizing_of_twoChildCong
    {firstScope secondScope parentScope : Nat}
    (wrapParent : RawTerm firstScope → RawTerm secondScope → RawTerm parentScope)
    (invertParentStep :
      ∀ {firstChild : RawTerm firstScope} {secondChild : RawTerm secondScope}
        {targetParent : RawTerm parentScope},
        Step (wrapParent firstChild secondChild) targetParent →
          (∃ targetFirst : RawTerm firstScope,
            targetParent = wrapParent targetFirst secondChild ∧
              Step firstChild targetFirst)
          ∨
          (∃ targetSecond : RawTerm secondScope,
            targetParent = wrapParent firstChild targetSecond ∧
              Step secondChild targetSecond))
    {firstChild : RawTerm firstScope}
    (firstTerminates : IsStronglyNormalizing firstChild)
    {secondChild : RawTerm secondScope}
    (secondTerminates : IsStronglyNormalizing secondChild) :
    IsStronglyNormalizing (wrapParent firstChild secondChild) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm secondScope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing (wrapParent currentFirst currentSecond))
    (m := fun currentFirst _ firstChildIH => by
      intro currentSecond currentSecondTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            IsStronglyNormalizing (wrapParent currentFirst innerSecond))
          (m := fun currentSecond currentSecondSuccessors secondChildIH =>
            Acc.intro (wrapParent currentFirst currentSecond)
              (fun targetParent parentStep => by
                cases invertParentStep parentStep with
                | inl firstBranch =>
                    obtain ⟨targetFirst, targetEq, firstStep⟩ := firstBranch
                    rw [targetEq]
                    exact firstChildIH targetFirst firstStep
                      (Acc.intro currentSecond currentSecondSuccessors)
                | inr secondBranch =>
                    obtain ⟨targetSecond, targetEq, secondStep⟩ :=
                      secondBranch
                    rw [targetEq]
                    exact secondChildIH targetSecond secondStep))
          currentSecondTerminates)
    firstTerminates)
    secondTerminates

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

/-- Cubical path abstraction is strongly normalizing when its body is strongly
normalizing.  The body lives under one fresh interval binder, matching the
lambda proof shape exactly at the raw substrate level. -/
theorem pathLam_isStronglyNormalizing_of_body {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyTerminates : IsStronglyNormalizing body) :
    IsStronglyNormalizing
      (.mkGen .gen_pathLam () (.childCons body .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope + 1)
    (parentScope := scope)
    (fun currentBody =>
      (.mkGen .gen_pathLam () (.childCons currentBody .childNil) :
        RawTerm scope))
    (fun parentStep => Step.from_pathLam parentStep)
    bodyTerminates

/-- Differential lambda abstraction is strongly normalizing when its body is
strongly normalizing.  Its raw binder shape mirrors ordinary lambda
abstraction. -/
theorem diffLambda_isStronglyNormalizing_of_body {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyTerminates : IsStronglyNormalizing body) :
    IsStronglyNormalizing
      (.mkGen .gen_diffLambda () (.childCons body .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope + 1)
    (parentScope := scope)
    (fun currentBody =>
      (.mkGen .gen_diffLambda () (.childCons currentBody .childNil) :
        RawTerm scope))
    (fun parentStep => Step.from_diffLambda parentStep)
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

/-- Modal introduction is strongly normalizing when its payload is strongly
normalizing.  Raw modal eta remains in `Step.eta`; beta+iota `Step` only has
congruence through this child. -/
theorem modIntro_isStronglyNormalizing_of_value {scope : Nat}
    {modalTerm : RawTerm scope}
    (modalTerminates : IsStronglyNormalizing modalTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_modIntro () (.childCons modalTerm .childNil) :
        RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentModal =>
      (.mkGen .gen_modIntro ()
        (.childCons currentModal .childNil) : RawTerm scope))
    (fun parentStep => Step.from_modIntro parentStep)
    modalTerminates

/-- Pairs are strongly normalizing when both components are strongly
normalizing. -/
theorem pair_isStronglyNormalizing_of_components {scope : Nat}
    {first second : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second) :
    IsStronglyNormalizing
      (.mkGen .gen_pair ()
        (.childCons first (.childCons second .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentFirst currentSecond =>
      (.mkGen .gen_pair ()
        (.childCons currentFirst (.childCons currentSecond .childNil)) :
          RawTerm scope))
    (fun parentStep => Step.from_pair parentStep)
    firstTerminates
    secondTerminates

/-- List cons is strongly normalizing when both its head and tail are strongly
normalizing. -/
theorem listCons_isStronglyNormalizing_of_head_tail {scope : Nat}
    {headVal tailVal : RawTerm scope}
    (headTerminates : IsStronglyNormalizing headVal)
    (tailTerminates : IsStronglyNormalizing tailVal) :
    IsStronglyNormalizing
      (.mkGen .gen_listCons ()
        (.childCons headVal (.childCons tailVal .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentHead currentTail =>
      (.mkGen .gen_listCons ()
        (.childCons currentHead (.childCons currentTail .childNil)) :
          RawTerm scope))
    (fun parentStep => Step.from_listCons parentStep)
    headTerminates
    tailTerminates

/-- Glue introduction is strongly normalizing when both the base and partial
payloads are strongly normalizing. -/
theorem glueIntro_isStronglyNormalizing_of_components {scope : Nat}
    {baseValue partialValue : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseValue)
    (partialTerminates : IsStronglyNormalizing partialValue) :
    IsStronglyNormalizing
      (.mkGen .gen_glueIntro ()
        (.childCons baseValue (.childCons partialValue .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentBase currentPartial =>
      (.mkGen .gen_glueIntro ()
        (.childCons currentBase (.childCons currentPartial .childNil)) :
          RawTerm scope))
    (fun parentStep => Step.from_glueIntro parentStep)
    baseTerminates
    partialTerminates

/-- Arrow type codes are strongly normalizing when both endpoint type codes are
strongly normalizing. -/
theorem arrowCode_isStronglyNormalizing_of_domain_codomain {scope : Nat}
    {domain codomain : RawTerm scope}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain) :
    IsStronglyNormalizing
      (.mkGen .gen_arrowCode ()
        (.childCons domain (.childCons codomain .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentDomain currentCodomain =>
      (.mkGen .gen_arrowCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_arrowCode parentStep)
    domainTerminates
    codomainTerminates

/-- Product type codes are strongly normalizing when both component type codes
are strongly normalizing. -/
theorem productCode_isStronglyNormalizing_of_left_right {scope : Nat}
    {leftType rightType : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType) :
    IsStronglyNormalizing
      (.mkGen .gen_productCode ()
        (.childCons leftType (.childCons rightType .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentLeftType currentRightType =>
      (.mkGen .gen_productCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_productCode parentStep)
    leftTypeTerminates
    rightTypeTerminates

/-- Sum type codes are strongly normalizing when both summand type codes are
strongly normalizing. -/
theorem sumCode_isStronglyNormalizing_of_left_right {scope : Nat}
    {leftType rightType : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType) :
    IsStronglyNormalizing
      (.mkGen .gen_sumCode ()
        (.childCons leftType (.childCons rightType .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentLeftType currentRightType =>
      (.mkGen .gen_sumCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_sumCode parentStep)
    leftTypeTerminates
    rightTypeTerminates

/-- Either type codes are strongly normalizing when both side type codes are
strongly normalizing. -/
theorem eitherCode_isStronglyNormalizing_of_left_right {scope : Nat}
    {leftType rightType : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherCode ()
        (.childCons leftType (.childCons rightType .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentLeftType currentRightType =>
      (.mkGen .gen_eitherCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_eitherCode parentStep)
    leftTypeTerminates
    rightTypeTerminates

/-- Equivalence type codes are strongly normalizing when both carrier type
codes are strongly normalizing. -/
theorem equivCode_isStronglyNormalizing_of_source_target {scope : Nat}
    {sourceType targetType : RawTerm scope}
    (sourceTypeTerminates : IsStronglyNormalizing sourceType)
    (targetTypeTerminates : IsStronglyNormalizing targetType) :
    IsStronglyNormalizing
      (.mkGen .gen_equivCode ()
        (.childCons sourceType (.childCons targetType .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentSourceType currentTargetType =>
      (.mkGen .gen_equivCode ()
        (.childCons currentSourceType
          (.childCons currentTargetType .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_equivCode parentStep)
    sourceTypeTerminates
    targetTypeTerminates

/-- Pi-type codes are strongly normalizing when their domain and under-binder
codomain codes are strongly normalizing. -/
theorem piTyCode_isStronglyNormalizing_of_domain_codomain {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain) :
    IsStronglyNormalizing
      (.mkGen .gen_piTyCode ()
        (.childCons domain (.childCons codomain .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope + 1)
    (parentScope := scope)
    (fun currentDomain currentCodomain =>
      (.mkGen .gen_piTyCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_piTyCode parentStep)
    domainTerminates
    codomainTerminates

/-- Sigma-type codes are strongly normalizing when their domain and
under-binder codomain codes are strongly normalizing. -/
theorem sigmaTyCode_isStronglyNormalizing_of_domain_codomain {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain) :
    IsStronglyNormalizing
      (.mkGen .gen_sigmaTyCode ()
        (.childCons domain (.childCons codomain .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope + 1)
    (parentScope := scope)
    (fun currentDomain currentCodomain =>
      (.mkGen .gen_sigmaTyCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_sigmaTyCode parentStep)
    domainTerminates
    codomainTerminates

/-- Polynomial functor codes are strongly normalizing when their position type
and under-binder position family are strongly normalizing. -/
theorem polyFunctor_isStronglyNormalizing_of_position_type_family {scope : Nat}
    {positionType : RawTerm scope} {positionFamily : RawTerm (scope + 1)}
    (positionTypeTerminates : IsStronglyNormalizing positionType)
    (positionFamilyTerminates : IsStronglyNormalizing positionFamily) :
    IsStronglyNormalizing
      (.mkGen .gen_polyFunctor ()
        (.childCons positionType (.childCons positionFamily .childNil)) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope + 1)
    (parentScope := scope)
    (fun currentPositionType currentPositionFamily =>
      (.mkGen .gen_polyFunctor ()
        (.childCons currentPositionType
          (.childCons currentPositionFamily .childNil)) :
        RawTerm scope))
    (fun parentStep => Step.from_polyFunctor parentStep)
    positionTypeTerminates
    positionFamilyTerminates

end StepStar
end LeanFX2.Foundation.PolyCell.Core
