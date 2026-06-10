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

/-- The listElim cell — `gen_listElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 0, 0]`).  Author order `(motive, scrutinee, nilBranch, consBranch)`; emitted spine
`(motive, nilBranch, consBranch, scrutinee)` with the motive under one binder and the scrutinee LAST. -/
private abbrev listElimCellLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch
          (.childCons scrutinee .childNil))))

/-- The listElim cons-contractum `app (app (app consBranch head) tail) (listElim motive tail nilBranch
consBranch)` — the Phase-Z cons ι THREADS the same motive into the recursive call. -/
private abbrev listElimConsContractumLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  appCellLocal (appCellLocal (appCellLocal consBranch head) tail)
    (listElimCellLocal motive tail nilBranch consBranch)

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct — `listElim` twin.**  For a weak-head-normal
scrutinee `value`, the `listElim` cell is SN as soon as the motive + branches are SN, the branch interface holds,
and the cell's ι-reduct (the nil branch when `value = listNil`, the cons-contractum when `value = listCons head
tail`) is a member.  Phase-Z motive shape: a TRIPLE `Acc.ndrec` over (motive, nilBranch, consBranch) carrying the
interface forward via CR2; the scrutinee never steps (fixed-normal); the motive-congruence recurses on the motive
IH and the ι-reduct's `iotaReductMember` is supplied the CURRENT motive's SN; ι-reduct SN via CR1.  The
cons-branch congruence is three `Step.cong` layers deep (the cons branch sits under `app (app (app consBranch
head) tail)`). -/
theorem listElimNormalScrutineeCellStronglyNormalizing {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    {motive : RawTerm (scope + 1)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {value : RawTerm scope}
    (valueNormal : RawTerm.isStepNormalForm value)
    {nilBranch consBranch : RawTerm scope}
    (nilBranchMember : resultCandidate nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal (appCellLocal consBranch head) tail) result))
    (iotaReductMember : ∀ {currentMotive : RawTerm (scope + 1)} {currentNil currentCons : RawTerm scope},
        IsStronglyNormalizing currentMotive →
        resultCandidate currentNil →
        IsStronglyNormalizing currentCons →
        (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
          resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal (appCellLocal currentCons head) tail) result)) →
        ∀ {target : RawTerm scope},
          ((value = listNilCell ∧ target = currentNil) ∨
            (∃ head tail : RawTerm scope,
              value = listConsCell head tail ∧
                target = listElimConsContractumLocal currentMotive currentCons head tail currentNil)) →
          resultCandidate target) :
    IsStronglyNormalizing (listElimCellLocal motive value nilBranch consBranch) := by
  -- Phase-Z motive shape: the cell reduces by congruence in the motive + both branches (the scrutinee is
  -- fixed-normal); the two ι reducts go through `iotaReductMember`.  A TRIPLE accessibility recursion over
  -- (motive, nilBranch, consBranch), with the cons-ι reduct threading the current motive.
  suffices aux : ∀ currentMotive : RawTerm (scope + 1), IsStronglyNormalizing currentMotive →
      ∀ currentNil : RawTerm scope, IsStronglyNormalizing currentNil →
      ∀ currentCons : RawTerm scope, IsStronglyNormalizing currentCons →
        resultCandidate currentNil →
        (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
          resultCandidate result →
          resultCandidate (appCellLocal (appCellLocal (appCellLocal currentCons head) tail) result)) →
        IsStronglyNormalizing (listElimCellLocal currentMotive value currentNil currentCons) by
    exact aux motive motiveStronglyNormalizing nilBranch (candidateMembersSN nilBranchMember) consBranch
      consBranchTerminates nilBranchMember consBranchApplication
  intro currentMotive currentMotiveSN
  induction currentMotiveSN with
  | intro motiveNode _motiveNodeAcc motiveIH =>
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
          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
          ⟨nilAfter, targetIsNilStep, nilStep⟩ |
          ⟨consAfter, targetIsConsStep, consStep⟩ |
          ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
        · rw [targetIsNil]
          exact candidateMembersSN
            (iotaReductMember (Acc.intro motiveNode _motiveNodeAcc) nilNodeMember
              (Acc.intro consNode consNodeAcc) consNodeApp (Or.inl ⟨valueIsNil, rfl⟩))
        · rw [targetIsContractum]
          exact candidateMembersSN
            (iotaReductMember (Acc.intro motiveNode _motiveNodeAcc) nilNodeMember
              (Acc.intro consNode consNodeAcc) consNodeApp
              (Or.inr ⟨headVal, tailVal, valueIsCons, rfl⟩))
        · rw [targetIsMotiveStep]
          exact motiveIH motiveAfter motiveStep nilNode (Acc.intro nilNode _nilNodeAcc) consNode
            (Acc.intro consNode consNodeAcc) nilNodeMember consNodeApp
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
        · exact absurd scrutineeStep
            (RawTerm.isStepNormalForm_blocks_step valueNormal scrutineeAfter)

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
    ∀ (motive : RawTerm (scope + 1)) (nilBranch consBranch : RawTerm scope),
      IsStronglyNormalizing motive →
      resultCandidate nilBranch →
      IsStronglyNormalizing consBranch →
      (∀ {head tail result : RawTerm scope}, RawTerm.isStepNormalForm head → IsListValue tail →
        resultCandidate result →
        resultCandidate (appCellLocal (appCellLocal (appCellLocal consBranch head) tail) result)) →
      resultCandidate (listElimCellLocal motive value nilBranch consBranch) := by
  induction valueIsList with
  | nil =>
      intro motive nilBranch consBranch motiveSN nilBranchMember consBranchSN consBranchApplication
      have cellSN :
          IsStronglyNormalizing (listElimCellLocal motive listNilCell nilBranch consBranch) :=
        listElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN (isListValue_impliesStepNormalForm IsListValue.nil)
          nilBranchMember consBranchSN consBranchApplication
          (by
            intro _currentMotive currentNil currentCons _currentMotiveSN currentNilMember
              _currentConsSN _currentConsApp target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_head, _tail, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentNilMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember cellSN
  | @cons head tail headNormal tailIsValue tailIH =>
      intro motive nilBranch consBranch motiveSN nilBranchMember consBranchSN consBranchApplication
      have cellSN :
          IsStronglyNormalizing
            (listElimCellLocal motive (listConsCell head tail) nilBranch consBranch) :=
        listElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN
          (isListValue_impliesStepNormalForm (IsListValue.cons headNormal tailIsValue))
          nilBranchMember consBranchSN consBranchApplication
          (by
            intro currentMotive currentNil currentCons currentMotiveSN currentNilMember
              currentConsSN currentConsApp target reductCase
            rcases reductCase with ⟨valueEq, _targetEq⟩ | ⟨headV, tailV, valueEq, targetEq⟩
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq)
            · injection valueEq with _equationOne _equationTwo _equationThree childrenEq
              injection childrenEq with _scopeEqA _shiftEqA _restShiftsEqA headEq tailChildrenEq
              injection tailChildrenEq with _scopeEqB _shiftEqB _restShiftsEqB tailEq
              subst headEq
              subst tailEq
              rw [targetEq]
              -- the cons-ι reduct's recursive listElim is at the CURRENT (possibly-stepped) motive;
              -- `tailIH` is re-invoked at `currentMotive` (it now universally quantifies the motive).
              exact currentConsApp headNormal tailIsValue
                (tailIH currentMotive currentNil currentCons currentMotiveSN currentNilMember
                  currentConsSN currentConsApp))
      have contractumMember :
          resultCandidate (listElimConsContractumLocal motive consBranch head tail nilBranch) :=
        consBranchApplication headNormal tailIsValue
          (tailIH motive nilBranch consBranch motiveSN nilBranchMember consBranchSN
            consBranchApplication)
      exact headExpand IotaHeadStep.iotaListElimCons.toWeakHeadStep contractumMember cellSN

end FX1Poly.Core
