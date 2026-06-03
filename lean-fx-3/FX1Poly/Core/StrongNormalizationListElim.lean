import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/StrongNormalizationListElim
    — the recursive-eliminator iota-redex SN: listElim cons case (toward SN-064)

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
redex-SN building block toward SN-064 (List reducibility + listElim); the list-WF-recursion tie-up is the
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
second recursive-eliminator iota-redex SN (toward SN-064), after `natElim`. -/
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

end StepStar
end FX1Poly.Core
