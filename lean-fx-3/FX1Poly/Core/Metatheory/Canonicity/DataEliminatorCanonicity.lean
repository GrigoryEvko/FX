import FX1Poly.Core.Eliminators.Core.NatElimDataTaitMember
import FX1Poly.Core.Eliminators.Core.NatRecDataTaitMember
import FX1Poly.Core.Eliminators.Core.ListElimDataTaitMember

/-! # FX1Poly/Core/Metatheory/Canonicity/DataEliminatorCanonicity
    — closed-scope canonicity for the RECURSIVE data eliminators (FTGEN-11.5), zero-axiom

This is the genuine payoff of the value-aware eliminator fundamental theorem — the thing the choice-free
strong-normalization arms (`InterpretsType.fundamentalNatElim` and friends) only GESTURED at.  Those arms
conclude "the eliminator cell is strongly normalizing"; here we conclude the strictly stronger
fundamental-theorem fact: at closed scope a recursor cell built from reducible pieces **computes to a
constructor**.

The engine is `natElimDataTaitMemberSelfContained` / `natRecDataTaitMemberSelfContained`: a recursor whose
scrutinee is a member of the Nat data candidate (`dataTaitCandidate IsNatValue`) and whose branches satisfy
their own fundamental-theorem closures lands in the RESULT data candidate `dataTaitCandidate isValue`.  Two
points of honesty about that engine, both inherited here:

  * the recursive call's membership is **discharged**, not assumed — `natElimValueMemberSelfContained`
    performs the recursion internally via the structural `IsNatValue` induction, so the only branch premise
    is the recursion-FREE `succBranchSubstClosed` (substituting a member recursive result + a numeral
    predecessor into the succ branch lands in the candidate);
  * the residual `succContractumTerminates` premise CANNOT be dropped: it is the recursor's
    strong-normalization obligation over an arbitrary strongly-normalizing predecessor, and raw `natElim` /
    `natRec` are NOT unconditionally strongly normalizing (they are partial-class generators).  That premise
    is exactly what reducibility supplies in the assembled typed fundamental theorem.

At CLOSED scope, membership becomes canonicity by `dataTaitCandidate.closedReducesToValue`: the neutral
disjunct is ruled out (`IsNeutral.noClosed` — no closed term is a stuck eliminator), so the cell's reachable
normal form is a value.  The result is conditional on the reducibility hypotheses (scrutinee reducible,
branches reducible, the succ branch's substitution-closure, the recursor-SN obligation) — precisely the
hypotheses a well-typed derivation discharges.  UNCONDITIONAL closed canonicity is the typed fundamental
theorem assembled over the `HasTypeDescPi` typing engine; this file is its data-recursor core.

## Zero-axiom verification

Each theorem is a direct composition: the shipped value-aware engine then
`dataTaitCandidate.closedReducesToValue`.  The `succContractumTerminates` premise is written in explicit
substitution form (definitionally equal to the engine's private successor-contractum abbreviation).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **★ Closed `natElim` canonicity — a closed recursor cell built from reducible pieces reduces to a
constructor of its result type.**  Given a closed scrutinee that is a member of the Nat data candidate, a
strongly-normalizing motive, a reducible zero-branch, a strongly-normalizing succ-branch, the recursion-free
succ-branch substitution-closure, and the recursor's strong-normalization obligation, the closed
`natElim` cell reduces (`StepStar`) to a normal-form VALUE of its result type (`isValue`).  This is the
fundamental theorem's computational payoff for the canonical recursive eliminator: not merely "strongly
normalizing", but "computes to a constructor".  The recursive-call membership is discharged internally; only
the reducibility-supplied recursor-SN premise remains. -/
theorem closedNatElimReducesToConstructor {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsNatValue scrutinee)
    (zeroBranchMember : dataTaitCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchSubstClosed :
        ∀ (currentMotive : RawTerm 1) (currentZero : RawTerm 0)
          (currentSucc : RawTerm 2) (predecessor recursiveResult : RawTerm 0),
          IsStronglyNormalizing currentMotive → dataTaitCandidate isValue currentZero →
          IsStronglyNormalizing currentSucc → IsNatValue predecessor →
          dataTaitCandidate isValue recursiveResult →
          dataTaitCandidate isValue (RawTerm.subst
            (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor)) currentSucc))
    (succContractumTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (RawTerm.subst
              (RawTermSubst.cons
                (.mkGen .gen_natElim ()
                  (.childCons currentMotive
                    (.childCons currentZero
                      (.childCons currentSucc
                        (.childCons predecessor .childNil)))))
                (RawTermSubst.singleton predecessor))
              currentSucc)) :
    ∃ value : RawTerm 0,
      StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch) value
        ∧ isValue value ∧ RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue
    (natElimDataTaitMemberSelfContained motiveStronglyNormalizing scrutineeMember
      zeroBranchMember succBranchTerminates succBranchSubstClosed succContractumTerminates)

/-- **★ Closed `natRec` canonicity** — the dependent-recursor twin of `closedNatElimReducesToConstructor`.
Same shape, `gen_natRec` successor-contractum, via `natRecDataTaitMemberSelfContained`: a closed dependent
recursor built from reducible pieces reduces to a constructor of its result type. -/
theorem closedNatRecReducesToConstructor {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsNatValue scrutinee)
    (zeroBranchMember : dataTaitCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchSubstClosed :
        ∀ (currentMotive : RawTerm 1) (currentZero : RawTerm 0)
          (currentSucc : RawTerm 2) (predecessor recursiveResult : RawTerm 0),
          IsStronglyNormalizing currentMotive → dataTaitCandidate isValue currentZero →
          IsStronglyNormalizing currentSucc → IsNatValue predecessor →
          dataTaitCandidate isValue recursiveResult →
          dataTaitCandidate isValue (RawTerm.subst
            (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor)) currentSucc))
    (succContractumTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (RawTerm.subst
              (RawTermSubst.cons
                (.mkGen .gen_natRec ()
                  (.childCons currentMotive
                    (.childCons currentZero
                      (.childCons currentSucc
                        (.childCons predecessor .childNil)))))
                (RawTermSubst.singleton predecessor))
              currentSucc)) :
    ∃ value : RawTerm 0,
      StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch) value
        ∧ isValue value ∧ RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue
    (natRecDataTaitMemberSelfContained motiveStronglyNormalizing scrutineeMember
      zeroBranchMember succBranchTerminates succBranchSubstClosed succContractumTerminates)

/-- **★ Closed `listElim` canonicity** — the list-recursor member of the family.  `listElim`'s cons ι fires
to a nested `gen_app` spine (the cons branch applied to head, tail, and the recursive `listElim` result), not
a substitution, so the recursive piece enters as the recursion-FREE `consBranchApplication`.  Via
`listElimDataTaitMember`, a closed `listElim` built from a reducible scrutinee and reducible branches reduces
to a constructor of its result type. -/
theorem closedListElimReducesToConstructor {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee nilBranch consBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsListValue scrutinee)
    (nilBranchMember : dataTaitCandidate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm 0},
        RawTerm.isStepNormalForm head → IsListValue tail → dataTaitCandidate isValue result →
        dataTaitCandidate isValue (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                (.childCons tail .childNil)))
            (.childCons result .childNil))))
    (consContractumTerminates :
        ∀ head tail : RawTerm 0, IsStronglyNormalizing head → IsStronglyNormalizing tail →
          IsStronglyNormalizing
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons
                    (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                    (.childCons tail .childNil)))
                (.childCons
                  (.mkGen .gen_listElim ()
                    (.childCons motive
                      (.childCons nilBranch
                        (.childCons consBranch (.childCons tail .childNil)))))
                  .childNil)))) :
    ∃ value : RawTerm 0,
      StepStar (listElimCellSpine motive scrutinee nilBranch consBranch) value
        ∧ isValue value ∧ RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue
    (listElimDataTaitMember motiveStronglyNormalizing scrutineeMember
      nilBranchMember consBranchTerminates consBranchApplication consContractumTerminates)

end FX1Poly.Core
