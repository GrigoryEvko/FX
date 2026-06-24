import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate

/-! # FX1Poly/Core/ListElimStructuredMemberStrongNormalization
    — recursor cell-SN for the BINARY recursor `listElim` (⚠ VACUOUS — see below)

⚠ RETRACTION (2026-06-24, commit fa10413c): the `listElimCellSpine_isStronglyNormalizing_of_structuredMember`
theorems below are VACUOUSLY conditional on a FALSE premise and are DEAD (audit-gated only, NO live importer) —
RETIREMENT CANDIDATES.  Their `consBranchApplicationClosed` premise quantifies the cons / nil branch and the
recursive cell over arbitrary SN terms; it is refuted by `tail := nil`, `nilBranch := lam (app (var 0) (var 0))`,
`consBranch := lam (lam (lam (app (var 0) (var 0))))` — the cons-ι app-spine reduces to `(λx. x x)(λx. x x) = Ω`,
NOT SN, because APPLICATION / SUBSTITUTION DOES NOT PRESERVE SN.  So these do NOT refute the
`consContractumTerminates` residue (identical defect): they merely relocate it.  Genuine list-recursor SN at an
open scrutinee needs REDUCIBILITY (member-valued branches), per
`Typed/Metatheory/Reducibility/Fundamental/ClosedNativeStronglyNormalizing.lean` and task #1754.  The
structural-descent SKELETON is sound; only the SN-valued application-closure premise is the flaw.

The `listElim` twin of `NatElimStructuredMemberStrongNormalization`, with the two differences forced by the BINARY
`listCons` constructor (as in `listElimDependentReducibleMember`):

  * the `cons`-ι does NOT substitute — it fires to the NESTED `gen_app` spine
    `app (app (app consBranch head) tail) (listElim motive nilBranch consBranch tail)` (`listElimConsContractum`),
    so the firing discharge produces SN of that app-spine rather than of a substituted branch;
  * the outer structural recursion descends the TAIL (the `cons` constructor's recursive argument); the head is
    carried (it appears in the app-spine, never as a recursion site) and contributes only its strong
    normalization.

Otherwise the construction is identical to the nat engine: a four-fold `Acc StepSuccessor` (scrutinee outermost,
then the three branches motive/nil/cons) whose scrutinee fold discharges the scrutinee-congruence arm via the
scrutinee IH (CR2 keeps the reduct a member; confluence — `stepStar_focus_reaches_normal_target` — keeps it
reaching the normal target), with the ι-cons firing supplied by the `consFiringDischarge` callback; and a combine
that does the structural `IsListStructured` induction, supplying that callback from the OUTER hypothesis at the
structurally-smaller tail (`listConsStructuredMember_tail` + the binary `listCons` congruence inversion
`stepStar_under_binaryCell`) at the `cons` node, and vacuously at the `nil` / `neutralNormal` leaves (a `listCons`
cell never reaches `listNil` or a neutral).  Never the over-general `consContractumTerminates` residue.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro`, the pinned `Step.from_listElim` inversion, `stepStar_focus_reaches_normal_target`,
`stepStar_under_binaryCell listConsCell Step.from_listCons`, the structured-list CR2
(`dataTaitCandidate.closedUnderStep`), and the list shape helpers.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- The `listElim` cons-ι contractum — `app (app (app consBranch head) tail) (listElim motive nilBranch consBranch
tail)` (mirrors Core's private `listElimConsContractum` byte-for-byte; the recursive `listElim` subterm is
`listElimCellSpine motive tail nilBranch consBranch`). -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app ()
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
        .childNil))

/-- **★ The residue-free binary-recursor cell-SN inner engine for a structured-member scrutinee.**  A `listElim`
cell whose scrutinee is a member of the structured List candidate, reaches a NORMAL structured target, and has
strongly-normalizing branches, is strongly normalizing — given the ι-cons firing obligation `consFiringDischarge`
(the app-spine contractum is SN whenever the scrutinee is a `listConsCell head tail` reaching the target).  A
four-fold `Acc StepSuccessor` (scrutinee outermost, then motive/nil/cons): scrutinee-congruence recurses via the
scrutinee IH (CR2 + confluence), ι-nil lands on the current nil branch, ι-cons on `consFiringDischarge`, the three
branch congruences recurse.  The binary `listCons` twin of
`natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching`. -/
theorem listElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching {scope : Nat}
    {structuredTarget : RawTerm scope}
    (structuredTargetIsNormal : RawTerm.isStepNormalForm structuredTarget)
    (consFiringDischarge :
      ∀ {currentScrutinee head tail : RawTerm scope},
        dataTaitCandidate IsListStructured currentScrutinee →
        StepStar currentScrutinee structuredTarget →
        currentScrutinee = listConsCell head tail →
        ∀ (currentMotive : RawTerm (scope + 1)) (currentNil currentCons : RawTerm scope),
          IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentNil →
          IsStronglyNormalizing currentCons →
          IsStronglyNormalizing
            (listElimConsContractum currentMotive currentCons head tail currentNil)) :
    ∀ {scrutinee : RawTerm scope},
      dataTaitCandidate IsListStructured scrutinee →
      StepStar scrutinee structuredTarget →
      ∀ {motive : RawTerm (scope + 1)} {nilBranch consBranch : RawTerm scope},
        IsStronglyNormalizing motive → IsStronglyNormalizing nilBranch → IsStronglyNormalizing consBranch →
        IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  intro scrutinee scrutineeMember
  refine
    (Acc.ndrec
      (r := StepSuccessor)
      (C := fun innerScrutinee =>
        dataTaitCandidate IsListStructured innerScrutinee →
        StepStar innerScrutinee structuredTarget →
        ∀ {motive : RawTerm (scope + 1)} {nilBranch consBranch : RawTerm scope},
          IsStronglyNormalizing motive → IsStronglyNormalizing nilBranch → IsStronglyNormalizing consBranch →
          IsStronglyNormalizing (listElimCellSpine motive innerScrutinee nilBranch consBranch))
      (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
        intro currentMember currentReaches motive nilBranch consBranch
          motiveTerminates nilBranchTerminates consBranchTerminates
        exact
          (Acc.ndrec
            (r := StepSuccessor)
            (C := fun innerMotive =>
              ∀ {currentNil : RawTerm scope} {currentCons : RawTerm scope},
                IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
                IsStronglyNormalizing (listElimCellSpine innerMotive currentScrutinee currentNil currentCons))
            (m := fun currentMotive currentMotiveSuccessors motiveIH => by
              intro currentNil currentCons currentNilTerminates currentConsTerminates
              exact
                (Acc.ndrec
                  (r := StepSuccessor)
                  (C := fun innerNil =>
                    ∀ {laterCons : RawTerm scope},
                      IsStronglyNormalizing laterCons →
                      IsStronglyNormalizing (listElimCellSpine currentMotive currentScrutinee innerNil laterCons))
                  (m := fun currentInnerNil currentInnerNilSuccessors nilIH => by
                    intro laterCons laterConsTerminates
                    exact
                      Acc.ndrec
                        (r := StepSuccessor)
                        (C := fun innerCons =>
                          IsStronglyNormalizing
                            (listElimCellSpine currentMotive currentScrutinee currentInnerNil innerCons))
                        (m := fun currentInnerCons currentInnerConsSuccessors consIH => by
                          apply Acc.intro
                          intro target step
                          rcases Step.from_listElim step with
                            ⟨_scrutineeIsNil, targetIsNil⟩ |
                            ⟨head, tail, scrutineeIsCons, targetIsContractum⟩ |
                            ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                            ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                            ⟨consAfter, targetIsConsStep, consStep⟩ |
                            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                          · rw [targetIsNil]
                            exact Acc.intro currentInnerNil currentInnerNilSuccessors
                          · rw [targetIsContractum]
                            exact consFiringDischarge currentMember currentReaches scrutineeIsCons
                              currentMotive currentInnerNil currentInnerCons
                              (Acc.intro currentMotive currentMotiveSuccessors)
                              (Acc.intro currentInnerNil currentInnerNilSuccessors)
                              (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          · rw [targetIsMotiveStep]
                            exact motiveIH motiveAfter motiveStep
                              (Acc.intro currentInnerNil currentInnerNilSuccessors)
                              (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          · rw [targetIsNilStep]
                            exact nilIH nilAfter nilStep
                              (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          · rw [targetIsConsStep]
                            exact consIH consAfter consStep
                          · rw [targetIsScrutineeStep]
                            exact scrutineeIH scrutineeAfter scrutineeStep
                              (currentMember.closedUnderStep scrutineeStep)
                              (stepStar_focus_reaches_normal_target currentMember.1
                                (StepStar.single scrutineeStep) currentReaches structuredTargetIsNormal)
                              (Acc.intro currentMotive currentMotiveSuccessors)
                              (Acc.intro currentInnerNil currentInnerNilSuccessors)
                              (Acc.intro currentInnerCons currentInnerConsSuccessors))
                        laterConsTerminates)
                  currentNilTerminates)
                  currentConsTerminates)
            motiveTerminates)
            nilBranchTerminates consBranchTerminates)
      scrutineeMember.1)
    scrutineeMember

/-- **★ The residue-free membership-based binary-recursor cell SN — `listElim` (FTGEN-13.1).**  A `listElim` cell
over a structured List member is strongly normalizing WITHOUT the over-general `consContractumTerminates` residue.
Structural induction on the structured value the scrutinee reaches: the ι-cons firing is discharged from the OUTER
hypothesis at the structurally-smaller TAIL (`listConsStructuredMember_tail` + the binary `listCons` congruence
inversion realignment), with the head's strong normalization carried (`listConsCell_head_isStronglyNormalizing`)
and the app-spine landed by `consBranchApplicationClosed`; the nil/neutral leaves' firings are vacuous.  The
branches are quantified in the inductive conclusion so the outer hypothesis applies at the recursive call's
(possibly stepped) branches.  `consBranchApplicationClosed` is the genuine fundamental-theorem-of-the-branch
content (a strongly-normalizing head, a member tail, and a strongly-normalizing recursive cell land the app-spine
SN), carrying no recursion. -/
theorem listElimCellSpine_isStronglyNormalizing_of_structuredMember {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplicationClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentNil currentCons head tail : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentNil →
        IsStronglyNormalizing currentCons → IsStronglyNormalizing head →
        dataTaitCandidate IsListStructured tail →
        IsStronglyNormalizing (listElimCellSpine currentMotive tail currentNil currentCons) →
        IsStronglyNormalizing
          (listElimConsContractum currentMotive currentCons head tail currentNil))
    (scrutineeMember : dataTaitCandidate IsListStructured scrutinee) :
    IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    listStructuredMemberReachesStructuredValue scrutineeMember
  suffices aux : ∀ {structured : RawTerm scope}, IsListStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsListStructured currentScrutinee →
        StepStar currentScrutinee structured →
        ∀ {currentMotive : RawTerm (scope + 1)} {currentNil currentCons : RawTerm scope},
          IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentNil →
          IsStronglyNormalizing currentCons →
          IsStronglyNormalizing (listElimCellSpine currentMotive currentScrutinee currentNil currentCons) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
      motiveTerminates nilBranchTerminates consBranchTerminates
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | nil =>
      refine listElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        (isListStructured_impliesStepNormalForm IsListStructured.nil) ?_
      intro currentScrutinee head tail currentMember currentReaches currentEquation
        _currentMotive _currentNil _currentCons _ _ _
      have reachesNil : StepStar (listConsCell head tail) listNilCell := currentEquation ▸ currentReaches
      obtain ⟨_headAfter, _tailAfter, nilEqualsCons, _, _⟩ :=
        stepStar_under_binaryCell listConsCell Step.from_listCons reachesNil head tail rfl
      exact Generator.noConfusion (congrArg RawTerm.rootGenerator nilEqualsCons)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      refine listElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        neutralTermIsNormal ?_
      intro currentScrutinee head tail currentMember currentReaches currentEquation
        _currentMotive _currentNil _currentCons _ _ _
      have reachesNeutral : StepStar (listConsCell head tail) neutralTerm := currentEquation ▸ currentReaches
      obtain ⟨_headAfter, _tailAfter, neutralEqualsCons, _, _⟩ :=
        stepStar_under_binaryCell listConsCell Step.from_listCons reachesNeutral head tail rfl
      exact (isNeutral_rootGenerator_ne_listCons (neutralEqualsCons ▸ neutralTermIsNeutral) rfl).elim
  | @cons valueHead valueTail valueHeadNormal valueTailIsStructured outerInductiveHypothesis =>
      refine listElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured)) ?_
      intro currentScrutinee head tail currentMember currentReaches currentEquation
        currentMotive currentNil currentCons currentMotiveSN currentNilSN currentConsSN
      have reachesCons : StepStar (listConsCell head tail) (listConsCell valueHead valueTail) :=
        currentEquation ▸ currentReaches
      obtain ⟨_headAfter, tailAfter, consEquation, _headReachesAfter, tailReachesAfter⟩ :=
        stepStar_under_binaryCell listConsCell Step.from_listCons reachesCons head tail rfl
      have tailAfterEqualsValue : tailAfter = valueTail := by
        injection consEquation with _equationOne _equationTwo _equationThree childrenEquation
        injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation _headEquation restEquation
        injection restEquation with _scopeEquationTwo _shiftEquationTwo _restShiftsEquationTwo tailEquation
        exact tailEquation.symm
      subst tailAfterEqualsValue
      have focusMember : dataTaitCandidate IsListStructured (listConsCell head tail) :=
        currentEquation ▸ currentMember
      have headStronglyNormalizing : IsStronglyNormalizing head :=
        listConsCell_head_isStronglyNormalizing focusMember.1
      have tailMember : dataTaitCandidate IsListStructured tail :=
        listConsStructuredMember_tail focusMember
      have recursiveCellSN :
          IsStronglyNormalizing (listElimCellSpine currentMotive tail currentNil currentCons) :=
        outerInductiveHypothesis tailMember tailReachesAfter
          currentMotiveSN currentNilSN currentConsSN
      exact consBranchApplicationClosed currentMotive currentNil currentCons head tail
        currentMotiveSN currentNilSN currentConsSN headStronglyNormalizing tailMember recursiveCellSN

end StepStar
end FX1Poly.Core
