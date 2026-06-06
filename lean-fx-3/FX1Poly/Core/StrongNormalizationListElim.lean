import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/StrongNormalizationListElim
    — the recursive-eliminator iota-redex SN: listElim cons case

`StrongNormalizationNatElim.lean` shipped the first recursive-eliminator iota-redex SN (the `natElim`
successor case).  This file does the second recursive data type — `List` — whose recursive ι-rule

```
listElim (listCons head tail) nilBranch consBranch
  ↝ app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)
```

contracts to a TRIPLE-nested application whose innermost right argument is the RECURSIVE CALL
`listElim tail …`.  Unlike `natElim` (where the successor scrutinee `natSucc pred` is one-child), the `List`
scrutinee `listCons head tail` is TWO-child, so the cons ι-arm extracts both `head` and `tail` and the
contractum is fed BOTH their strong-normalization facts.  This file ships:

* `headValue_isStronglyNormalizing_of_listCons` / `tailValue_isStronglyNormalizing_of_listCons` — the two
  one-child-projection subterm-SN lemmas for `listCons` (head and tail of a strongly-normalizing cons are
  strongly normalizing), the `gen_listCons` mirrors of `firstComponent_of_pair` / `secondComponent_of_pair`.
* `listElim_isStronglyNormalizing_of_normal_branches` — the conditional cons-case iota-redex SN: with both
  branches normal and the cons contractum strongly normalizing for every strongly-normalizing head and tail,
  a `listElim` redex with a strongly-normalizing scrutinee is strongly normalizing.

As in the `natElim` case, the `consContractumTerminates` hypothesis is the honest IH-carrying premise — it
asserts the contractum (which contains the recursive `listElim tail …` call) is SN for every SN head/tail,
exactly the obligation the eventual well-founded recursion on the list structure discharges.  This is the
redex-SN building block toward List reducibility + listElim; the list-WF-recursion tie-up is the
remaining content.

## Zero-axiom verification

The two subterm lemmas are `Acc` well-founded recursion generalized over the `listCons` term (each head/tail
step lifts to a `listCons` step via `StepChildren.here` / `StepChildren.there ∘ here`), mirroring the pair
projections.  The redex SN is `Acc.ndrec` on the scrutinee; `Step.from_listElim` splits the five arms — ι-nil
lands on the normal `nilBranch`, ι-cons on the contractum (discharged by `consContractumTerminates` at the two
subterm-SN projections), scrutinee-congruence by the induction hypothesis, and the two branch-congruences are
impossible (the branches are normal).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The head of a strongly-normalizing `listCons` is strongly normalizing.**  The first one-child-projection
subterm-SN lemma for `listCons`: each head step lifts to a `listCons` step (head congruence
`StepChildren.here`), so accessibility of `listCons head tail` descends to `head`.  The `gen_listCons` mirror
of `firstComponent_isStronglyNormalizing_of_pair`. -/
theorem headValue_isStronglyNormalizing_of_listCons {scope : Nat}
    {headValue tailValue : RawTerm scope}
    (consTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing headValue := by
  suffices general :
      ∀ {consTerm : RawTerm scope}, Acc StepSuccessor consTerm →
        ∀ {currentHead currentTail : RawTerm scope},
          consTerm = .mkGen .gen_listCons ()
            (.childCons currentHead (.childCons currentTail .childNil)) →
          Acc StepSuccessor currentHead from
    general consTerminates rfl
  intro consTerm consAccessible
  induction consAccessible with
  | intro consWitness _consPredecessors consInductiveHypothesis =>
      intro currentHead currentTail witnessEq
      subst witnessEq
      apply Acc.intro
      intro headAfter headStep
      have congruenceLift :
          Step
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons currentTail .childNil)) : RawTerm scope)
            (.mkGen .gen_listCons ()
              (.childCons headAfter (.childCons currentTail .childNil)) : RawTerm scope) :=
        Step.cong .gen_listCons ()
          (StepChildren.here
            (.childCons currentTail .childNil : RawTermChildren [0] scope) headStep)
      exact consInductiveHypothesis
        (.mkGen .gen_listCons () (.childCons headAfter (.childCons currentTail .childNil)))
        congruenceLift rfl

/-- **The tail of a strongly-normalizing `listCons` is strongly normalizing.**  The second
one-child-projection subterm-SN lemma: each tail step lifts via the tail-then-head congruence
(`StepChildren.there ∘ StepChildren.here`), so accessibility of `listCons head tail` descends to `tail`.  The
`gen_listCons` mirror of `secondComponent_isStronglyNormalizing_of_pair`; the `there` binder shift is pinned
with the explicit `@`-form because `gen_listCons.binderShifts = [0, 0]` does not auto-reduce. -/
theorem tailValue_isStronglyNormalizing_of_listCons {scope : Nat}
    {headValue tailValue : RawTerm scope}
    (consTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing tailValue := by
  suffices general :
      ∀ {consTerm : RawTerm scope}, Acc StepSuccessor consTerm →
        ∀ {currentHead currentTail : RawTerm scope},
          consTerm = .mkGen .gen_listCons ()
            (.childCons currentHead (.childCons currentTail .childNil)) →
          Acc StepSuccessor currentTail from
    general consTerminates rfl
  intro consTerm consAccessible
  induction consAccessible with
  | intro consWitness _consPredecessors consInductiveHypothesis =>
      intro currentHead currentTail witnessEq
      subst witnessEq
      apply Acc.intro
      intro tailAfter tailStep
      have congruenceLift :
          Step
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons currentTail .childNil)) : RawTerm scope)
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons tailAfter .childNil)) : RawTerm scope) :=
        Step.cong .gen_listCons ()
          (@StepChildren.there scope 0 [0] currentHead _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) tailStep))
      exact consInductiveHypothesis
        (.mkGen .gen_listCons () (.childCons currentHead (.childCons tailAfter .childNil)))
        congruenceLift rfl

/-- **The listElim cons-case iota-redex is strongly normalizing.**  With both branches normal and the cons
contractum strongly normalizing for every strongly-normalizing head and tail, a `listElim` redex with a
strongly-normalizing scrutinee is strongly normalizing.  `Acc.ndrec` runs on the scrutinee;
`Step.from_listElim` gives the five arms: ι-nil → the normal `nilBranch`; ι-cons → the contractum, discharged
by `consContractumTerminates` at the head/tail subterm-SN projections of the accessible `listCons` scrutinee;
scrutinee-congruence → the induction hypothesis; branch-congruences → impossible by branch normality.  The
second recursive-eliminator iota-redex SN, after `natElim`. -/
theorem listElim_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (nilBranchHasNoStep : ∀ targetNil : RawTerm scope, Step nilBranch targetNil → False)
    (consBranchHasNoStep : ∀ targetCons : RawTerm scope, Step consBranch targetCons → False)
    (consContractumTerminates :
      ∀ {headValue tailValue : RawTerm scope},
        IsStronglyNormalizing headValue → IsStronglyNormalizing tailValue →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons consBranch (.childCons headValue .childNil)))
                  (.childCons tailValue .childNil)))
              (.childCons
                (.mkGen .gen_listElim ()
                  (.childCons tailValue
                    (.childCons nilBranch (.childCons consBranch .childNil))))
                .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_listElim ()
          (.childCons currentScrutinee
            (.childCons nilBranch (.childCons consBranch .childNil))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_listElim ()
          (.childCons currentScrutinee
            (.childCons nilBranch (.childCons consBranch .childNil))) :
          RawTerm scope)
        (fun targetTerm listElimStep => by
          rcases Step.from_listElim listElimStep with
            ⟨_scrutineeIsNil, targetIsNil⟩ |
            ⟨headValue, tailValue, scrutineeIsCons, targetIsContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨nilAfter, _targetIsNilStep, nilStep⟩ |
            ⟨consAfter, _targetIsConsStep, consStep⟩
          · rw [targetIsNil]
            exact isStronglyNormalizing_of_noStep nilBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsCons] at currentScrutineeSN
            exact consContractumTerminates
              (headValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
              (tailValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd nilStep (nilBranchHasNoStep nilAfter)
          · exact absurd consStep (consBranchHasNoStep consAfter)))
    scrutineeTerminates

/-- The listElim cons-contractum `app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)`. -/
private abbrev listElimConsContractum {scope : Nat} (consBranch head tail nilBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons tail (.childCons nilBranch (.childCons consBranch .childNil))))
        .childNil))

/-- **The listElim redex is strongly normalizing from SN (not necessarily normal) branches.**  The SN-branch
strengthening of `listElim_isStronglyNormalizing_of_normal_branches`, required for recursor REDUCIBILITY:
in the Tait/data-candidate argument the branches are MEMBERS (hence SN) but not normal.  The list twin
of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches`: a triple nested accessibility induction on
`(scrutinee, nilBranch, consBranch)` with the cons-contractum SN hypothesis (now over two values — `head` and
`tail`) THREADED through both branch inductions.  Under `nilBranch`-congruence the update is one hop (the nil
branch occurs once, inside the recursive `listElim`); under `consBranch`-congruence it is TWO hops (the cons
branch occurs in `app (app consBranch head) tail` — three app layers deep — AND in the recursive `listElim`),
each discharged by app/listElim congruence + `IsStronglyNormalizing.inv`. -/
theorem listElim_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum consBranch head tail nilBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentNil currentCons : RawTerm scope},
        IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
          (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
            IsStronglyNormalizing (listElimConsContractum currentCons head tail currentNil)) →
          IsStronglyNormalizing
            (.mkGen .gen_listElim ()
              (.childCons currentScrutinee
                (.childCons currentNil (.childCons currentCons .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentNil currentCons currentNilTerminates currentConsTerminates currentConsContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerNil =>
            ∀ {currentCons : RawTerm scope},
              IsStronglyNormalizing currentCons →
                (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                  IsStronglyNormalizing (listElimConsContractum currentCons head tail innerNil)) →
                IsStronglyNormalizing
                  (.mkGen .gen_listElim ()
                    (.childCons currentScrutinee
                      (.childCons innerNil (.childCons currentCons .childNil)))))
          (m := fun currentInnerNil currentInnerNilSuccessors nilIH => by
            intro currentCons currentConsTerminates currentInnerNilContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerCons =>
                  (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                    IsStronglyNormalizing (listElimConsContractum innerCons head tail currentInnerNil)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_listElim ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerNil (.childCons innerCons .childNil)))))
                (m := fun currentInnerCons currentInnerConsSuccessors consIH => by
                      intro currentInnerConsContractum
                      apply Acc.intro
                      intro targetTerm listElimStep
                      rcases Step.from_listElim listElimStep with
                        ⟨_scrutineeIsNil, targetIsNil⟩ |
                        ⟨headValue, tailValue, scrutineeIsCons, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                        ⟨consAfter, targetIsConsStep, consStep⟩
                      · rw [targetIsNil]
                        exact Acc.intro currentInnerNil currentInnerNilSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsCons] at currentScrutineeSN
                        exact currentInnerConsContractum headValue tailValue
                          (headValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                          (tailValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerNil currentInnerNilSuccessors)
                          (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          currentInnerConsContractum
                      · rw [targetIsNilStep]
                        refine nilIH nilAfter nilStep
                          (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          (fun head tail headTerminates tailTerminates => ?_)
                        exact (currentInnerConsContractum head tail headTerminates tailTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app () (.childCons currentInnerCons (.childCons head .childNil)))
                                  (.childCons tail .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_listElim ()
                                  (StepChildren.there (headShift := 0) tail
                                    (StepChildren.here
                                      (.childCons currentInnerCons .childNil : RawTermChildren [0] scope)
                                      nilStep))))))
                      · rw [targetIsConsStep]
                        refine consIH consAfter consStep (fun head tail headTerminates tailTerminates => ?_)
                        have hopOne :
                            Step (listElimConsContractum currentInnerCons head tail currentInnerNil)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons
                                      (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                      (.childCons tail .childNil)))
                                  (.childCons
                                    (.mkGen .gen_listElim ()
                                      (.childCons tail
                                        (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_listElim ()
                                  (.childCons tail
                                    (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons tail .childNil : RawTermChildren [0] scope)
                                  (Step.cong .gen_app ()
                                    (StepChildren.here
                                      (.childCons head .childNil : RawTermChildren [0] scope) consStep)))))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons
                                      (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                      (.childCons tail .childNil)))
                                  (.childCons
                                    (.mkGen .gen_listElim ()
                                      (.childCons tail
                                        (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                    .childNil)))
                              (listElimConsContractum consAfter head tail currentInnerNil) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                  (.childCons tail .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_listElim ()
                                  (StepChildren.there (headShift := 0) tail
                                    (StepChildren.there (headShift := 0) currentInnerNil
                                      (StepChildren.here .childNil consStep))))))
                        exact (((currentInnerConsContractum head tail headTerminates tailTerminates).inv
                          hopOne).inv hopTwo))
                currentConsTerminates currentInnerNilContractum)
          currentNilTerminates currentConsTerminates currentConsContractum))
    scrutineeTerminates)
    nilBranchTerminates consBranchTerminates consContractumTerminates

end StepStar
end FX1Poly.Core
