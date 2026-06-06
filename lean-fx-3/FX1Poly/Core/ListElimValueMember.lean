import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RecursiveEliminatorBaseComputation

/-! # FX1Poly/Core/ListElimValueMember
    — value-case `listElim` reducibility with the recursor-SN obligation DISCHARGED (the list twin of
      `NatElimValueMember`)

The list analogue of `NatElimValueMember`: `ListElimValueReducibility` proves the value case of `listElim`
recursor reducibility but takes `redexStronglyNormalizing` (the recursor cell at a list value is SN) as a bespoke
per-use hypothesis.  This file removes it for the value case, deriving the cell SN from the UNIVERSAL
reducibility-candidate properties — CR1 (`candidateMembersSN`) + CR2 (`candidateForwardClosed`) — plus
`consBranchTerminates` (the cons branch is SN, CR1 on the reducible cons-branch member).

The only structural difference from the Nat recursors is the cons branch: it takes a (normal) head AND a
list-value tail, so the cons-contractum is the three-deep application
`app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)`, and the `IsListValue.cons`
constructor carries `headNormal` + `tailIsValue`.  The scrutinee-fixed cell-SN recursor is otherwise identical:
a double `Acc.ndrec` over (nilBranch, consBranch) carrying the branch interface forward under congruence via CR2,
the scrutinee never steps (it is normal), and the ι-reduct is SN via CR1 on its membership.

Fundamental-independent: a fixed (non-universe-domain) result candidate; the pure Tait value-recursor argument for the
list eliminator.

## Zero-axiom verification

The helper is the double accessibility recursion + `Step.from_listElim` dispatch (scrutinee-step closed by
`RawTerm.isStepNormalForm_blocks_step`; the cross-constructor nil/cons impossibilities by `Generator.noConfusion`
∘ `congrArg RawTerm.rootGenerator`; the cons head+tail recovered by two `injection` drills through the
`childCons` dependent indices).  `listElimValueMember` is one `IsListValue` induction feeding the helper +
`headExpand`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (verified
by `#print axioms` in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open StepStar

/-- The application cell `app function argument`. -/
private abbrev appCellLocal {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

/-- The listElim cell over its (scrutinee, nilBranch, consBranch) spine. -/
private abbrev listElimCellLocal {scope : Nat} (scrutinee nilBranch consBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

/-- The listElim cons-contractum `app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)`. -/
private abbrev listElimConsContractumLocal {scope : Nat}
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal (appCellLocal consBranch head) tail)
    (listElimCellLocal tail nilBranch consBranch)

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct — `listElim` twin.**  For a weak-head-normal
scrutinee `value`, the `listElim` cell is SN as soon as the branches are SN, the branch interface holds, and the
cell's ι-reduct (the nil branch when `value = listNil`, the cons-contractum when `value = listCons head tail`) is
a member.  Double `Acc.ndrec` over (nilBranch, consBranch) carrying the interface forward via CR2; scrutinee
never steps; ι-reduct SN via CR1.  The cons-branch congruence is three `Step.cong` layers deep (the cons branch
sits under `app (app (app consBranch head) tail)`). -/
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

/-- **Value-case `listElim` reducibility, UNCONDITIONAL in the cell-SN dimension — the list twin of
`natElimValueMember`.**  CR1 + CR2 + `consBranchTerminates` replace the bespoke `redexStronglyNormalizing`, via
the `listElim` scrutinee-fixed cell-SN recursor; the cons-ι contractum's membership is supplied by the
`IsListValue` tail IH through `consBranchApplication`. -/
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
