import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RecursiveEliminatorBaseComputation

/-! # FX1Poly/Core/NatElimValueMember
    — value-case `natElim` / `natRec` reducibility with the recursor-SN obligation DISCHARGED

`NatElimValueReducibility` proves the value case of `natElim` recursor reducibility — `natElim numeral
zeroBranch succBranch` lands in the result candidate — but takes `redexStronglyNormalizing` (the recursor cell at
a numeral is strongly normalizing) as a bespoke per-use HYPOTHESIS, discharged downstream by the
SN-from-SN-branches recursor fed the honest `succContractumTerminates` IH-premise.

This file removes that bespoke obligation for the VALUE case: it derives the cell SN directly from the
UNIVERSAL reducibility-candidate properties — CR1 (`candidateMembersSN`: members are strongly normalizing) and
CR2 (`candidateForwardClosed`: membership is preserved forward under `Step`) — plus `succBranchTerminates` (the
succ branch is SN, which is CR1 on the reducible succ-branch member).  The point is that the recursor cell at a
numeral is SN by a scrutinee-fixed accessibility recursion whose ι-reduct SN comes from the branch-application
behaviour (a member, hence SN by CR1), NOT from a bespoke `succContractumTerminates`.

Two theorems:

* `natElimNormalScrutineeCellStronglyNormalizing` — the load-bearing scrutinee-FIXED cell-SN recursor: for a
  weak-head-normal scrutinee `value`, the `natElim` cell is SN as soon as the branch interface holds and the
  cell's ι-reduct (the zero branch when `value = natZero`; the succ-contractum when `value = natSucc pred`) is a
  member.  Proved by a double `Acc.ndrec` over (zeroBranch, succBranch) carrying the branch interface forward
  under congruence via CR2; the scrutinee never steps (it is normal); the ι-reduct is SN via CR1 on its
  membership.  This is the value-scrutinee specialization of the SN-from-SN-branches recursor that replaces the
  bespoke `succContractumTerminates` with the universal CR2 + the member ι-reduct.
* `natElimValueMember` — value-case reducibility, with `redexStronglyNormalizing` discharged: by structural
  induction on `IsNatValue`, the cell SN comes from the helper (its succ-ι-reduct membership supplied by the
  `IsNatValue` membership IH), and the membership itself by weak-head expansion of the ι-reduct.

Fundamental-independent: the result candidate is a fixed (non-universe-domain) candidate; this is the pure
computational Tait recursor argument for the value case.  The scrutinee-reduction and neutral regimes are the
remaining outer recursion, shared with the closed-membership track.

## Zero-axiom verification

The helper is a double accessibility recursion + `Step.from_natElim` dispatch (the scrutinee-step case is closed
by `RawTerm.isStepNormalForm_blocks_step`; the cross-constructor ι impossibilities by `Generator.noConfusion`
∘ `congrArg RawTerm.rootGenerator`; the succ predecessor by `injection` through the dependent `childCons`
indices).  `natElimValueMember` is one `IsNatValue` induction feeding the helper + `headExpand`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms` in
scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open StepStar

/-- The application cell `app function argument`. -/
private abbrev appCellLocal {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

/-- The natElim cell over its (scrutinee, zeroBranch, succBranch) spine. -/
private abbrev natElimCellLocal {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The natElim succ-contractum `app (app succBranch pred) (natElim pred zeroBranch succBranch)`. -/
private abbrev natElimSuccContractumLocal {scope : Nat}
    (succBranch predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal succBranch predecessor)
    (natElimCellLocal predecessor zeroBranch succBranch)

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct.**  For a weak-head-normal scrutinee `value`
(`isStepNormalForm`), the `natElim` cell is strongly normalizing as soon as the branches are SN, the branch
interface (`zeroBranchMember` / `succBranchApplication`) holds, and the cell's ι-reduct (the zero branch when
`value = natZero`, the succ-contractum when `value = natSucc pred`) is a `resultCandidate` member for the current
branches.  Double `Acc.ndrec` over (zeroBranch, succBranch), carrying the branch interface forward under
congruence via CR2; the scrutinee never steps (it is normal); the ι-reduct is SN via CR1 on its membership. -/
theorem natElimNormalScrutineeCellStronglyNormalizing {scope : Nat}
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
                target = natElimSuccContractumLocal currentSucc predecessor currentZero)) →
          resultCandidate target) :
    IsStronglyNormalizing (natElimCellLocal value zeroBranch succBranch) := by
  suffices aux : ∀ currentZero : RawTerm scope, IsStronglyNormalizing currentZero →
      ∀ currentSucc : RawTerm scope, IsStronglyNormalizing currentSucc →
        resultCandidate currentZero →
        (∀ {predecessor result : RawTerm scope}, IsNatValue predecessor → resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal currentSucc predecessor) result)) →
        IsStronglyNormalizing (natElimCellLocal value currentZero currentSucc) by
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
      rcases Step.from_natElim step with
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

/-- **Value-case `natElim` reducibility, UNCONDITIONAL in the cell-SN dimension.**  Replaces
`natElimValueReducibility`'s bespoke `redexStronglyNormalizing` hypothesis with the universal candidate
properties CR1 (`candidateMembersSN`) + CR2 (`candidateForwardClosed`) plus `succBranchTerminates` (the succ
branch is SN — CR1 on the reducible succ-branch member): the recursor cell at a numeral is SN by the
scrutinee-fixed cell-SN recursor, with the succ-ι contractum's membership supplied by the `IsNatValue`
membership IH, and the membership itself by weak-head expansion of the ι-reduct. -/
theorem natElimValueMember {scope : Nat}
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
      resultCandidate (natElimCellLocal value zeroBranch succBranch) := by
  induction valueIsNat with
  | zero =>
      intro zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication
      have cellSN : IsStronglyNormalizing (natElimCellLocal natZeroCell zeroBranch succBranch) :=
        natElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed (isNatValue_impliesStepNormalForm IsNatValue.zero)
          zeroBranchMember succBranchSN succBranchApplication
          (by
            intro currentZero currentSucc currentZeroMember _currentSuccSN _currentSuccApp
              target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_pred, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentZeroMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember cellSN
  | @succ predecessor predecessorIsValue predecessorIH =>
      intro zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication
      have cellSN :
          IsStronglyNormalizing (natElimCellLocal (natSuccCell predecessor) zeroBranch succBranch) :=
        natElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
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
          resultCandidate (natElimSuccContractumLocal succBranch predecessor zeroBranch) :=
        succBranchApplication predecessorIsValue
          (predecessorIH zeroBranch succBranch zeroBranchMember succBranchSN succBranchApplication)
      exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep contractumMember cellSN

/-- The natRec cell over its (scrutinee, zeroBranch, succBranch) spine. -/
private abbrev natRecCellLocal {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_natRec ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The natRec succ-contractum `app (app succBranch pred) (natRec pred zeroBranch succBranch)`. -/
private abbrev natRecSuccContractumLocal {scope : Nat}
    (succBranch predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal succBranch predecessor)
    (natRecCellLocal predecessor zeroBranch succBranch)

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct — `natRec` twin.**  Identical structure to
`natElimNormalScrutineeCellStronglyNormalizing`; the dependent recursor `gen_natRec` has the same five-way
`Step.from_natRec` inversion and the same nested-application succ-contractum, so the same double `Acc.ndrec`
over the branches with the CR2-forward-stable interface applies. -/
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

/-- **Value-case `natRec` reducibility, UNCONDITIONAL in the cell-SN dimension — the `natRec` twin of
`natElimValueMember`.**  Same discharge: CR1 + CR2 + `succBranchTerminates` replace the bespoke
`redexStronglyNormalizing`, via the `natRec` scrutinee-fixed cell-SN recursor. -/
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
