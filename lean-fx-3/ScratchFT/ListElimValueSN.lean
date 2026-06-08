import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RecursiveEliminatorBaseComputation

namespace FX1Poly.Core
open StepStar

private abbrev appCellLocal {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

private abbrev listElimCellLocal {scope : Nat} (scrutinee nilBranch consBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

private abbrev listElimConsContractumLocal {scope : Nat}
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal (appCellLocal consBranch head) tail)
    (listElimCellLocal tail nilBranch consBranch)

theorem listElimNormalScrutineeCellStronglyNormalizing {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    {value : RawTerm scope}
    (valueNormal : RawTerm.isStepNormalForm value)
    {nilBranch consBranch : RawTerm scope}
    (nilBranchMember : resultCandidate nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal (appCellLocal consBranch head) tail) result))
    (iotaReductMember : ∀ {currentNil currentCons : RawTerm scope},
        resultCandidate currentNil →
        IsStronglyNormalizing currentCons →
        (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
          resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal (appCellLocal currentCons head) tail) result)) →
        ∀ {target : RawTerm scope},
          ((value = listNilCell ∧ target = currentNil) ∨
            (∃ head tail : RawTerm scope,
              value = listConsCell head tail ∧
                target = listElimConsContractumLocal currentCons head tail currentNil)) →
          resultCandidate target) :
    IsStronglyNormalizing (listElimCellLocal value nilBranch consBranch) := by
  suffices aux : ∀ currentNil : RawTerm scope, IsStronglyNormalizing currentNil →
      ∀ currentCons : RawTerm scope, IsStronglyNormalizing currentCons →
        resultCandidate currentNil →
        (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
          resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal (appCellLocal currentCons head) tail) result)) →
        IsStronglyNormalizing (listElimCellLocal value currentNil currentCons) by
    exact aux nilBranch (candidateMembersSN nilBranchMember) consBranch consBranchTerminates
      nilBranchMember consBranchApplication
  intro currentNil currentNilSN
  induction currentNilSN with
  | intro nilNode _nilNodeAcc nilIH =>
    intro currentCons currentConsSN
    induction currentConsSN with
    | intro consNode consNodeAcc consIH =>
      intro nilNodeMember consNodeApp
      apply Acc.intro
      intro target step
      rcases Step.from_listElim step with
        ⟨valueIsNil, targetIsNil⟩ |
        ⟨headVal, tailVal, valueIsCons, targetIsContractum⟩ |
        ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩ |
        ⟨nilAfter, targetIsNilStep, nilStep⟩ |
        ⟨consAfter, targetIsConsStep, consStep⟩
      · rw [targetIsNil]
        exact candidateMembersSN
          (iotaReductMember nilNodeMember (Acc.intro consNode consNodeAcc) consNodeApp
            (Or.inl ⟨valueIsNil, rfl⟩))
      · rw [targetIsContractum]
        exact candidateMembersSN
          (iotaReductMember nilNodeMember (Acc.intro consNode consNodeAcc) consNodeApp
            (Or.inr ⟨headVal, tailVal, valueIsCons, rfl⟩))
      · exact absurd scrutineeStep
          (RawTerm.isStepNormalForm_blocks_step valueNormal scrutineeAfter)
      · rw [targetIsNilStep]
        exact nilIH nilAfter nilStep consNode (Acc.intro consNode consNodeAcc)
          (candidateForwardClosed nilNodeMember nilStep) consNodeApp
      · rw [targetIsConsStep]
        refine consIH consAfter consStep nilNodeMember
          (fun headNormal tailIsValue resultMember => ?_)
        exact candidateForwardClosed (consNodeApp headNormal tailIsValue resultMember)
          (Step.cong .gen_app ()
            (StepChildren.here (.childCons _ .childNil)
              (Step.cong .gen_app ()
                (StepChildren.here (.childCons _ .childNil)
                  (Step.cong .gen_app ()
                    (StepChildren.here (.childCons _ .childNil) consStep))))))

theorem listElimValueMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    {value : RawTerm scope} (valueIsList : IsListValue value) :
    ∀ (nilBranch consBranch : RawTerm scope),
      resultCandidate nilBranch →
      IsStronglyNormalizing consBranch →
      (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
        resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal (appCellLocal consBranch head) tail) result)) →
      resultCandidate (listElimCellLocal value nilBranch consBranch) := by
  induction valueIsList with
  | nil =>
      intro nilBranch consBranch nilBranchMember consBranchSN consBranchApplication
      have cellSN : IsStronglyNormalizing (listElimCellLocal listNilCell nilBranch consBranch) :=
        listElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed (isListValue_impliesStepNormalForm IsListValue.nil)
          nilBranchMember consBranchSN consBranchApplication
          (by
            intro currentNil currentCons currentNilMember _currentConsSN _currentConsApp
              target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_head, _tail, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentNilMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember cellSN
  | @cons head tail headNormal tailIsValue tailIH =>
      intro nilBranch consBranch nilBranchMember consBranchSN consBranchApplication
      have cellSN :
          IsStronglyNormalizing (listElimCellLocal (listConsCell head tail) nilBranch consBranch) :=
        listElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed
          (isListValue_impliesStepNormalForm (IsListValue.cons headNormal tailIsValue))
          nilBranchMember consBranchSN consBranchApplication
          (by
            intro currentNil currentCons currentNilMember currentConsSN currentConsApp
              target reductCase
            rcases reductCase with ⟨valueEq, _targetEq⟩ | ⟨headV, tailV, valueEq, targetEq⟩
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq)
            · injection valueEq with _equationOne _equationTwo _equationThree childrenEq
              injection childrenEq with _scopeEqA _shiftEqA _restShiftsEqA headEq tailChildrenEq
              injection tailChildrenEq with _scopeEqB _shiftEqB _restShiftsEqB tailEq
              subst headEq
              subst tailEq
              rw [targetEq]
              exact currentConsApp headNormal tailIsValue
                (tailIH _ _ currentNilMember currentConsSN currentConsApp))
      have contractumMember :
          resultCandidate (listElimConsContractumLocal consBranch head tail nilBranch) :=
        consBranchApplication headNormal tailIsValue
          (tailIH nilBranch consBranch nilBranchMember consBranchSN consBranchApplication)
      exact headExpand IotaHeadStep.iotaListElimCons.toWeakHeadStep contractumMember cellSN

end FX1Poly.Core

#print axioms FX1Poly.Core.listElimNormalScrutineeCellStronglyNormalizing
#print axioms FX1Poly.Core.listElimValueMember
