import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RecursiveEliminatorBaseComputation

/-! # FX1Poly/Core/NatElimValueMember
    — value-case `natElim` / `natRec` reducibility with the recursor-SN obligation DISCHARGED

`NatElimValueReducibility` proves the value case of `natElim` recursor reducibility — `natElim motive
zeroBranch succBranch numeral` lands in the result candidate — but takes `redexStronglyNormalizing` (the
recursor cell at a numeral is strongly normalizing) as a bespoke per-use HYPOTHESIS, discharged downstream by
the SN-from-SN-branches recursor fed the honest substituted-reduct IH-premise.

This file removes that bespoke obligation for the VALUE case: it derives the cell SN directly from the
UNIVERSAL reducibility-candidate properties — CR1 (`candidateMembersSN`: members are strongly normalizing) and
CR2 (`candidateForwardClosed`: membership is preserved forward under `Step`) — plus the motive's SN and the
succ branch's SN (CR1 on the reducible succ-branch member).  The recursor cell at a numeral is SN by a
scrutinee-fixed accessibility recursion whose ι-reduct SN comes from the branch-application behaviour (a member,
hence SN by CR1), NOT from a bespoke recursor-SN premise.

**The substitution headline (why this is NOT the listElim pattern):** the `listElim` cons-iota reduct is the
app-chain `app (app (app consBranch head) tail) (listElim motive tail …)`, so under a branch step its reduct
relates to the stepped-branch reduct by an explicit congruence walk.  The `natElim` succ-iota reduct is the
SUBSTITUTION `succBranch[var 0 := natElim motive z s pred, var 1 := pred]` — there is NO `Step` relating
`subst σ[zeroBranch] succBranch` to `subst σ[zeroAfter] succBranch` by congruence (substitution can
duplicate/relocate the recursive call, which embeds the branches).  So — exactly as in the SN file
`StrongNormalizationNatElim` — the reduct-membership interface `succReductApplication` is UNIVERSALLY QUANTIFIED
over the current motive/zero/succ/predecessor, and every branch-congruence arm RE-INVOKES the cell-SN IH passing
the SAME universal premise re-instantiated at the stepped motive/branch — no `.inv` congruence hop.

Phase-Z motive shape (arity 4, `binderShifts [1, 0, 2, 0]`, spine `(motive, zeroBranch, succBranch, scrutinee)`
with the motive under one binder, the succ-branch under TWO binders, and the scrutinee LAST).  The value-case
`natElimValueMember` UNIVERSALLY QUANTIFIES the motive (and branches) in its `IsNatValue` induction tail (the
universal-in-conclusion recipe) because the recursion re-invokes the predecessor IH at the CURRENT
(possibly-stepped) motive.

Two theorems (per recursor):

* `natElimNormalScrutineeCellStronglyNormalizing` — the load-bearing scrutinee-FIXED cell-SN recursor: a TRIPLE
  `Acc.ndrec` over (motive, zeroBranch, succBranch) carrying the universal reduct-membership interface forward
  unchanged under congruence; the scrutinee never steps (fixed-normal); the two ι reducts are members via
  `iotaReductMember`; ι-reduct SN via CR1.
* `natElimValueMember` — value-case reducibility, with the recursor-SN obligation discharged: by structural
  induction on `IsNatValue` universally quantifying the motive/branches.

Fundamental-independent: the result candidate is a fixed (non-universe-domain) candidate; this is the pure
computational Tait recursor argument for the value case.  The scrutinee-reduction and neutral regimes are the
remaining outer recursion, shared with the closed-membership track.

## Zero-axiom verification

The helper is a triple accessibility recursion + `Step.from_natElim` dispatch (the scrutinee-step case is closed
by `RawTerm.isStepNormalForm_blocks_step`; the cross-constructor ι impossibilities by `Generator.noConfusion`
∘ `congrArg RawTerm.rootGenerator`; the succ predecessor by `injection` through the dependent `childCons`
indices).  `natElimValueMember` is one `IsNatValue` induction feeding the helper + `headExpand`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open StepStar

/-- The natElim cell — `gen_natElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 2, 0]`).  Author order `(motive, scrutinee, zeroBranch, succBranch)`; emitted spine
`(motive, zeroBranch, succBranch, scrutinee)` with the motive under one binder, the succ-branch under TWO
binders, and the scrutinee LAST. -/
private abbrev natElimCellLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The natElim succ-iota SUBSTITUTED reduct
`succBranch[var 0 := natElim motive zeroBranch succBranch predecessor, var 1 := predecessor]` — the Phase-Z
succ ι THREADS the same motive/branches into the recursive call (substituted for `var 0`) and the predecessor
into `var 1`. -/
private abbrev natElimSuccReductLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct — `natElim`.**  For a weak-head-normal scrutinee
`value`, the `natElim` cell is SN as soon as the motive + branches are SN and the cell's ι-reduct (the zero
branch when `value = natZero`, the succ-reduct when `value = natSucc pred`) is a member — supplied through
`iotaReductMember`.  Phase-Z SUBSTITUTING shape: a TRIPLE `Acc.ndrec` over (motive, zeroBranch, succBranch); the
scrutinee never steps (fixed-normal).  Because the succ-iota SUBSTITUTES, the reduct-membership interface
`succReductApplication` is UNIVERSAL over motive/predecessor and threaded UNCHANGED through every congruence arm
(the substitution analogue of the SN file's universal `succContractumTerminates`); ι-reduct SN via CR1. -/
theorem natElimNormalScrutineeCellStronglyNormalizing {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    {motive : RawTerm (scope + 1)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {value : RawTerm scope}
    (valueNormal : RawTerm.isStepNormalForm value)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succReductApplication :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
          IsNatValue predecessor →
          resultCandidate (natElimSuccReductLocal currentMotive currentZero currentSucc predecessor))
    (iotaReductMember :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)),
        IsStronglyNormalizing currentMotive →
        resultCandidate currentZero →
        IsStronglyNormalizing currentSucc →
        (∀ (innerMotive : RawTerm (scope + 1)) (innerZero : RawTerm scope)
            (innerSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
          resultCandidate (natElimSuccReductLocal innerMotive innerZero innerSucc predecessor)) →
        ∀ {target : RawTerm scope},
          ((value = natZeroCell ∧ target = currentZero) ∨
            (∃ predecessor : RawTerm scope,
              value = natSuccCell predecessor ∧
                target = natElimSuccReductLocal currentMotive currentZero currentSucc predecessor)) →
          resultCandidate target) :
    IsStronglyNormalizing (natElimCellLocal motive value zeroBranch succBranch) := by
  -- Phase-Z motive shape: the cell reduces by congruence in the motive + both branches (the scrutinee is
  -- fixed-normal); the two ι reducts go through `iotaReductMember`.  A TRIPLE accessibility recursion over
  -- (motive, zeroBranch, succBranch), with the universal reduct-membership interface threaded UNCHANGED.
  suffices aux : ∀ currentMotive : RawTerm (scope + 1), IsStronglyNormalizing currentMotive →
      ∀ currentZero : RawTerm scope, IsStronglyNormalizing currentZero →
      ∀ currentSucc : RawTerm (scope + 2), IsStronglyNormalizing currentSucc →
        resultCandidate currentZero →
        (∀ (innerMotive : RawTerm (scope + 1)) (innerZero : RawTerm scope)
            (innerSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
          resultCandidate (natElimSuccReductLocal innerMotive innerZero innerSucc predecessor)) →
        IsStronglyNormalizing (natElimCellLocal currentMotive value currentZero currentSucc) by
    exact aux motive motiveStronglyNormalizing zeroBranch (candidateMembersSN zeroBranchMember) succBranch
      succBranchTerminates zeroBranchMember succReductApplication
  intro currentMotive currentMotiveSN
  induction currentMotiveSN with
  | intro motiveNode _motiveNodeAcc motiveIH =>
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
          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
          ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
          ⟨succAfter, targetIsSuccStep, succStep⟩ |
          ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
        · rw [targetIsZero]
          exact candidateMembersSN
            (iotaReductMember motiveNode zeroNode succNode (Acc.intro motiveNode _motiveNodeAcc)
              zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp (Or.inl ⟨valueIsZero, rfl⟩))
        · rw [targetIsContractum]
          exact candidateMembersSN
            (iotaReductMember motiveNode zeroNode succNode (Acc.intro motiveNode _motiveNodeAcc)
              zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp
              (Or.inr ⟨predecessor, valueIsSucc, rfl⟩))
        · rw [targetIsMotiveStep]
          exact motiveIH motiveAfter motiveStep zeroNode (Acc.intro zeroNode _zeroNodeAcc) succNode
            (Acc.intro succNode succNodeAcc) zeroNodeMember succNodeApp
        · rw [targetIsZeroStep]
          exact zeroIH zeroAfter zeroStep succNode (Acc.intro succNode succNodeAcc)
            (candidateForwardClosed zeroNodeMember zeroStep) succNodeApp
        · rw [targetIsSuccStep]
          exact succIH succAfter succStep zeroNodeMember succNodeApp
        · exact absurd scrutineeStep
            (RawTerm.isStepNormalForm_blocks_step valueNormal scrutineeAfter)

/-- **Value-case `natElim` reducibility, UNCONDITIONAL in the cell-SN dimension.**  Replaces
`natElimValueReducibility`'s bespoke `redexStronglyNormalizing` hypothesis with the universal candidate
properties CR1 (`candidateMembersSN`) + CR2 (`candidateForwardClosed`) plus the motive's SN and the succ
branch's SN (CR1 on the reducible succ-branch member): the recursor cell at a numeral is SN by the
scrutinee-fixed cell-SN recursor, with the succ-ι SUBSTITUTED reduct's membership supplied by the `IsNatValue`
membership IH (re-invoked at the CURRENT motive — hence the motive is UNIVERSALLY QUANTIFIED in the induction
tail), and the membership itself by weak-head expansion of the ι-reduct. -/
theorem natElimValueMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    ∀ (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)),
      IsStronglyNormalizing motive →
      resultCandidate zeroBranch →
      IsStronglyNormalizing succBranch →
      (∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
        resultCandidate (natElimSuccReductLocal currentMotive currentZero currentSucc predecessor)) →
      resultCandidate (natElimCellLocal motive value zeroBranch succBranch) := by
  induction valueIsNat with
  | zero =>
      intro motive zeroBranch succBranch motiveSN zeroBranchMember succBranchSN succReductApplication
      have cellSN :
          IsStronglyNormalizing (natElimCellLocal motive natZeroCell zeroBranch succBranch) :=
        natElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN (isNatValue_impliesStepNormalForm IsNatValue.zero)
          zeroBranchMember succBranchSN succReductApplication
          (by
            intro currentMotive currentZero currentSucc _currentMotiveSN currentZeroMember
              _currentSuccSN _currentSuccApp target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_pred, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentZeroMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember cellSN
  | @succ predecessor predecessorIsValue _predecessorIH =>
      intro motive zeroBranch succBranch motiveSN zeroBranchMember succBranchSN succReductApplication
      have cellSN :
          IsStronglyNormalizing (natElimCellLocal motive (natSuccCell predecessor) zeroBranch succBranch) :=
        natElimNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN
          (isNatValue_impliesStepNormalForm (IsNatValue.succ predecessorIsValue))
          zeroBranchMember succBranchSN succReductApplication
          (by
            intro currentMotive currentZero currentSucc _currentMotiveSN currentZeroMember
              _currentSuccSN currentSuccApp target reductCase
            rcases reductCase with ⟨valueEq, _targetEq⟩ | ⟨pred, valueEq, targetEq⟩
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq)
            · injection valueEq with _equationOne _equationTwo _equationThree childrenEq
              injection childrenEq with _scopeEq _shiftEq _restShiftsEq predEq
              subst predEq
              rw [targetEq]
              exact currentSuccApp currentMotive currentZero currentSucc predecessor predecessorIsValue)
      exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep
        (succReductApplication motive zeroBranch succBranch predecessor predecessorIsValue) cellSN

/-- The natRec cell — `gen_natRec` in the Phase-Z motive shape (arity 4, `binderShifts = [1, 0, 2, 0]`). -/
private abbrev natRecCellLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) : RawTerm scope :=
  .mkGen .gen_natRec ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The natRec succ-iota SUBSTITUTED reduct — the `gen_natRec` mirror of `natElimSuccReductLocal`. -/
private abbrev natRecSuccReductLocal {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **Cell SN for a NORMAL scrutinee from a member ι-reduct — `natRec` twin.**  Identical structure to
`natElimNormalScrutineeCellStronglyNormalizing`; the dependent recursor `gen_natRec` has the same six-way
`Step.from_natRec` inversion and the same SUBSTITUTING succ-reduct, so the same triple `Acc.ndrec` over
(motive, zeroBranch, succBranch) with the universal reduct-membership interface threaded UNCHANGED applies. -/
theorem natRecNormalScrutineeCellStronglyNormalizing {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    {motive : RawTerm (scope + 1)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {value : RawTerm scope}
    (valueNormal : RawTerm.isStepNormalForm value)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succReductApplication :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
          IsNatValue predecessor →
          resultCandidate (natRecSuccReductLocal currentMotive currentZero currentSucc predecessor))
    (iotaReductMember :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)),
        IsStronglyNormalizing currentMotive →
        resultCandidate currentZero →
        IsStronglyNormalizing currentSucc →
        (∀ (innerMotive : RawTerm (scope + 1)) (innerZero : RawTerm scope)
            (innerSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
          resultCandidate (natRecSuccReductLocal innerMotive innerZero innerSucc predecessor)) →
        ∀ {target : RawTerm scope},
          ((value = natZeroCell ∧ target = currentZero) ∨
            (∃ predecessor : RawTerm scope,
              value = natSuccCell predecessor ∧
                target = natRecSuccReductLocal currentMotive currentZero currentSucc predecessor)) →
          resultCandidate target) :
    IsStronglyNormalizing (natRecCellLocal motive value zeroBranch succBranch) := by
  suffices aux : ∀ currentMotive : RawTerm (scope + 1), IsStronglyNormalizing currentMotive →
      ∀ currentZero : RawTerm scope, IsStronglyNormalizing currentZero →
      ∀ currentSucc : RawTerm (scope + 2), IsStronglyNormalizing currentSucc →
        resultCandidate currentZero →
        (∀ (innerMotive : RawTerm (scope + 1)) (innerZero : RawTerm scope)
            (innerSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
          resultCandidate (natRecSuccReductLocal innerMotive innerZero innerSucc predecessor)) →
        IsStronglyNormalizing (natRecCellLocal currentMotive value currentZero currentSucc) by
    exact aux motive motiveStronglyNormalizing zeroBranch (candidateMembersSN zeroBranchMember) succBranch
      succBranchTerminates zeroBranchMember succReductApplication
  intro currentMotive currentMotiveSN
  induction currentMotiveSN with
  | intro motiveNode _motiveNodeAcc motiveIH =>
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
          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
          ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
          ⟨succAfter, targetIsSuccStep, succStep⟩ |
          ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
        · rw [targetIsZero]
          exact candidateMembersSN
            (iotaReductMember motiveNode zeroNode succNode (Acc.intro motiveNode _motiveNodeAcc)
              zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp (Or.inl ⟨valueIsZero, rfl⟩))
        · rw [targetIsContractum]
          exact candidateMembersSN
            (iotaReductMember motiveNode zeroNode succNode (Acc.intro motiveNode _motiveNodeAcc)
              zeroNodeMember (Acc.intro succNode succNodeAcc) succNodeApp
              (Or.inr ⟨predecessor, valueIsSucc, rfl⟩))
        · rw [targetIsMotiveStep]
          exact motiveIH motiveAfter motiveStep zeroNode (Acc.intro zeroNode _zeroNodeAcc) succNode
            (Acc.intro succNode succNodeAcc) zeroNodeMember succNodeApp
        · rw [targetIsZeroStep]
          exact zeroIH zeroAfter zeroStep succNode (Acc.intro succNode succNodeAcc)
            (candidateForwardClosed zeroNodeMember zeroStep) succNodeApp
        · rw [targetIsSuccStep]
          exact succIH succAfter succStep zeroNodeMember succNodeApp
        · exact absurd scrutineeStep
            (RawTerm.isStepNormalForm_blocks_step valueNormal scrutineeAfter)

/-- **Value-case `natRec` reducibility, UNCONDITIONAL in the cell-SN dimension — the `natRec` twin of
`natElimValueMember`.**  Same discharge: CR1 + CR2 + motive/succ SN replace the bespoke
`redexStronglyNormalizing`, via the `natRec` scrutinee-fixed cell-SN recursor; the motive is universally
quantified in the `IsNatValue` induction tail. -/
theorem natRecValueMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (candidateForwardClosed :
      ∀ {term reduct : RawTerm scope}, resultCandidate term → Step term reduct → resultCandidate reduct)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    ∀ (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)),
      IsStronglyNormalizing motive →
      resultCandidate zeroBranch →
      IsStronglyNormalizing succBranch →
      (∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope), IsNatValue predecessor →
        resultCandidate (natRecSuccReductLocal currentMotive currentZero currentSucc predecessor)) →
      resultCandidate (natRecCellLocal motive value zeroBranch succBranch) := by
  induction valueIsNat with
  | zero =>
      intro motive zeroBranch succBranch motiveSN zeroBranchMember succBranchSN succReductApplication
      have cellSN :
          IsStronglyNormalizing (natRecCellLocal motive natZeroCell zeroBranch succBranch) :=
        natRecNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN (isNatValue_impliesStepNormalForm IsNatValue.zero)
          zeroBranchMember succBranchSN succReductApplication
          (by
            intro currentMotive currentZero currentSucc _currentMotiveSN currentZeroMember
              _currentSuccSN _currentSuccApp target reductCase
            rcases reductCase with ⟨_valueEq, targetEq⟩ | ⟨_pred, valueEq, _targetEq⟩
            · rw [targetEq]; exact currentZeroMember
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq))
      exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember cellSN
  | @succ predecessor predecessorIsValue _predecessorIH =>
      intro motive zeroBranch succBranch motiveSN zeroBranchMember succBranchSN succReductApplication
      have cellSN :
          IsStronglyNormalizing (natRecCellLocal motive (natSuccCell predecessor) zeroBranch succBranch) :=
        natRecNormalScrutineeCellStronglyNormalizing resultCandidate candidateMembersSN
          candidateForwardClosed motiveSN
          (isNatValue_impliesStepNormalForm (IsNatValue.succ predecessorIsValue))
          zeroBranchMember succBranchSN succReductApplication
          (by
            intro currentMotive currentZero currentSucc _currentMotiveSN currentZeroMember
              _currentSuccSN currentSuccApp target reductCase
            rcases reductCase with ⟨valueEq, _targetEq⟩ | ⟨pred, valueEq, targetEq⟩
            · exact Generator.noConfusion (congrArg RawTerm.rootGenerator valueEq)
            · injection valueEq with _equationOne _equationTwo _equationThree childrenEq
              injection childrenEq with _scopeEq _shiftEq _restShiftsEq predEq
              subst predEq
              rw [targetEq]
              exact currentSuccApp currentMotive currentZero currentSucc predecessor predecessorIsValue)
      exact headExpand IotaHeadStep.iotaNatRecSucc.toWeakHeadStep
        (succReductApplication motive zeroBranch succBranch predecessor predecessorIsValue) cellSN

end FX1Poly.Core
