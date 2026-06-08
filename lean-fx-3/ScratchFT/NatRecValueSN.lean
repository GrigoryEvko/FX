import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RecursiveEliminatorBaseComputation

namespace FX1Poly.Core
open StepStar

private abbrev appCellLocal {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

private abbrev natRecCellLocal {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_natRec ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

private abbrev natRecSuccContractumLocal {scope : Nat}
    (succBranch predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal succBranch predecessor)
    (natRecCellLocal predecessor zeroBranch succBranch)

theorem natRecNormalScrutineeCellStronglyNormalizing {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    {value : RawTerm scope}
    (valueNormal : RawTerm.isStepNormalForm value)
    {zeroBranch succBranch : RawTerm scope}
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal succBranch predecessor) result))
    (iotaReductMember : ∀ {currentZero currentSucc : RawTerm scope},
        resultCandidate currentZero →
        IsStronglyNormalizing currentSucc →
        (∀ {predecessor result : RawTerm scope}, IsNatValue predecessor → resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal currentSucc predecessor) result)) →
        ∀ {target : RawTerm scope},
          ((value = natZeroCell ∧ target = currentZero) ∨
            (∃ predecessor : RawTerm scope,
              value = natSuccCell predecessor ∧
                target = natRecSuccContractumLocal currentSucc predecessor currentZero)) →
          resultCandidate target) :
    IsStronglyNormalizing (natRecCellLocal value zeroBranch succBranch) := by
  suffices aux : ∀ currentZero : RawTerm scope, IsStronglyNormalizing currentZero →
      ∀ currentSucc : RawTerm scope, IsStronglyNormalizing currentSucc →
        resultCandidate currentZero →
        (∀ {predecessor result : RawTerm scope}, IsNatValue predecessor → resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal currentSucc predecessor) result)) →
        IsStronglyNormalizing (natRecCellLocal value currentZero currentSucc) by
    exact aux zeroBranch (candidateMembersSN zeroBranchMember) succBranch succBranchTerminates
      zeroBranchMember succBranchApplication
  intro currentZero currentZeroSN
  induction currentZeroSN with
  | intro zeroNode _zeroNodeAcc zeroIH =>
    intro currentSucc currentSuccSN
    induction currentSuccSN with
    | intro succNode succNodeAcc succIH =>
      intro zeroNodeMember succNodeApp
      apply Acc.intro
      intro target step
      rcases Step.from_natRec step with
        ⟨valueIsZero, targetIsZero⟩ |
        ⟨predecessor, valueIsSucc, targetIsContractum⟩ |
        ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩ |
        ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
        ⟨succAfter, targetIsSuccStep, succStep⟩
      · rw [targetIsZero]
        exact candidateMembersSN
          (iotaReductMember zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp
            (Or.inl ⟨valueIsZero, rfl⟩))
      · rw [targetIsContractum]
        exact candidateMembersSN
          (iotaReductMember zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp
            (Or.inr ⟨predecessor, valueIsSucc, rfl⟩))
      · exact absurd scrutineeStep
          (RawTerm.isStepNormalForm_blocks_step valueNormal scrutineeAfter)
      · rw [targetIsZeroStep]
        exact zeroIH zeroAfter zeroStep succNode (Acc.intro succNode succNodeAcc)
          (candidateForwardClosed zeroNodeMember zeroStep) succNodeApp
      · rw [targetIsSuccStep]
        refine succIH succAfter succStep zeroNodeMember (fun predIsValue resultMember => ?_)
        exact candidateForwardClosed (succNodeApp predIsValue resultMember)
          (Step.cong .gen_app ()
            (StepChildren.here (.childCons _ .childNil)
              (Step.cong .gen_app ()
                (StepChildren.here (.childCons _ .childNil) succStep))))

theorem natRecValueMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    ∀ (zeroBranch succBranch : RawTerm scope),
      resultCandidate zeroBranch →
      IsStronglyNormalizing succBranch →
      (∀ {predecessor result : RawTerm scope}, IsNatValue predecessor → resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal succBranch predecessor) result)) →
      resultCandidate (natRecCellLocal value zeroBranch succBranch) := by
  induction valueIsNat with
  | zero =>
      intro zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication
      have cellSN : IsStronglyNormalizing (natRecCellLocal natZeroCell zeroBranch succBranch) :=
        natRecNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed (isNatValue_impliesStepNormalForm IsNatValue.zero)
          zeroBranchMember succBranchSN succBranchApplication
          (by
            intro currentZero currentSucc currentZeroMember _currentSuccSN _currentSuccApp
              target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_pred, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentZeroMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember cellSN
  | @succ predecessor predecessorIsValue predecessorIH =>
      intro zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication
      have cellSN :
          IsStronglyNormalizing (natRecCellLocal (natSuccCell predecessor) zeroBranch succBranch) :=
        natRecNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed
          (isNatValue_impliesStepNormalForm (IsNatValue.succ predecessorIsValue))
          zeroBranchMember succBranchSN succBranchApplication
          (by
            intro currentZero currentSucc currentZeroMember currentSuccSN currentSuccApp
              target reductCase
            rcases reductCase with ⟨valueEq, _targetEq⟩ | ⟨pred, valueEq, targetEq⟩
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq)
            · injection valueEq with _equationOne _equationTwo _equationThree childrenEq
              injection childrenEq with _scopeEq _shiftEq _restShiftsEq predEq
              subst predEq
              rw [targetEq]
              exact currentSuccApp predecessorIsValue
                (predecessorIH _ _ currentZeroMember currentSuccSN currentSuccApp))
      have contractumMember :
          resultCandidate (natRecSuccContractumLocal succBranch predecessor zeroBranch) :=
        succBranchApplication predecessorIsValue
          (predecessorIH zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication)
      exact headExpand IotaHeadStep.iotaNatRecSucc.toWeakHeadStep contractumMember cellSN

end FX1Poly.Core

#print axioms FX1Poly.Core.natRecNormalScrutineeCellStronglyNormalizing
#print axioms FX1Poly.Core.natRecValueMember
