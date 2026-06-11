import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/IotaHeadStep
    — deterministic root-iota reduction for eliminator-headed codes

`HeadStep` (`HeadStep.lean`) captures the β half of weak-head reduction: contract the head β-redex, or
head-reduce into the function spine.  This file captures the COMPLEMENTARY ι half: contract the
eliminator-on-constructor redex AT THE ROOT — `boolElim m t e boolTrue ↝ t`, `natRec m z s (natSucc p) ↝
s[var 0 := natRec m z s p, var 1 := p]`, etc. — and nothing else (no congruence, no reduction into the
scrutinee).

Why a separate root-only relation (rather than reusing `Step`'s ι constructors): like `HeadStep.beta`,
the point is DETERMINISM.  At a fixed eliminator-headed code with a constructor scrutinee, exactly one ι
rule fires and its contractum is unique — the root generator plus the scrutinee constructor pick the
rule, and the rule's contractum is a function of the redex.  That determinism is what a weak-head-normal
dispatching reducibility relation needs to stay functional once large elimination lets an eliminator
appear AS A TYPE-CODE (`natRec`-at-a-universe, a roadmap item): such a code is NOT `HeadStep`-reducible
(it is `gen_natRec`-rooted, not `gen_app`-rooted) yet it is a genuine root redex, so the
`ReducibleType.neutral` arm (`¬ HeadStep ∧ root ≠ piTyCode → SN`) would mis-classify it.  `IotaHeadStep`
is the substrate the large-elimination-ready `iotaExpand` companion arm will dispatch on, exactly as
`headExpand` dispatches on `HeadStep`.  It is also the reduction characterization the typed ι subject-
reduction, the weak-head normalizer, and the Path-B convergent rewrite presentation consume.

The sixteen rules are the same redex/contractum pairs as `Step`'s ι constructors (§11.6.1 SHAPE 1-5),
restricted to the root: SHAPE 1 branch-selection (bool×2 / nat-zero×2 / list-nil / option-none / idJ-refl
/ idStrictRec-refl), SHAPE 2 content-projection (pair fst/snd), SHAPE 3 1-arg app-chain (option-some /
either-inl/inr), SHAPE 4 SUBSTITUTING with recursion (natElim/natRec on succ — the Phase-Z two-binder
succ-branch receives the recursive call and the predecessor by direct substitution), SHAPE 5 3-arg
app-chain (listElim on cons).

## Zero-axiom verification

A sixteen-constructor inductive `Prop` + determinism by `cases` on both derivations (each off-diagonal
pair is impossible — distinct root generators or distinct scrutinee constructors — and is discharged by
index unification, the propext-clean route used throughout the ι subject-reduction family) + `toStep` by
forward constructor mapping.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Root-iota reduction.**  Contract an eliminator-on-constructor redex at the root.  Deterministic by
construction: the root generator and scrutinee constructor select a unique rule with a unique
contractum.  No congruence — reduction into the scrutinee is a separate concern (mirrors how `HeadStep`
keeps β-at-the-head separate from reduction into arguments). -/
inductive IotaHeadStep {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- `boolElim motive thenBranch elseBranch boolTrue ↝ thenBranch`.
      Phase-Z motive shape: motive first (under one binder), scrutinee last;
      the iota discards the motive operationally. -/
  | iotaBoolTrue {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))))
        thenBranch
  /-- `boolElim motive thenBranch elseBranch boolFalse ↝ elseBranch`. -/
  | iotaBoolFalse {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))))
        elseBranch
  /-- `fst (pair firstValue secondValue) ↝ firstValue`. -/
  | iotaFstPair {firstValue secondValue : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_fst ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        firstValue
  /-- `snd (pair firstValue secondValue) ↝ secondValue`. -/
  | iotaSndPair {firstValue secondValue : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_snd ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        secondValue
  /-- `natElim motive zeroBranch succBranch natZero ↝ zeroBranch`.
      Phase-Z motive shape: motive first (under one binder), succ-branch
      under two binders, scrutinee last; the base-case iota discards
      the motive operationally. -/
  | iotaNatElimZero {motive : RawTerm (scope + 1)}
      {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaHeadStep
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
        zeroBranch
  /-- `natRec motive zeroBranch succBranch natZero ↝ zeroBranch`. -/
  | iotaNatRecZero {motive : RawTerm (scope + 1)}
      {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaHeadStep
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
        zeroBranch
  /-- `listElim motive nilBranch consBranch listNil ↝ nilBranch`.
      Phase-Z motive shape: motive first (under one binder), scrutinee last;
      the base-case iota discards the motive operationally. -/
  | iotaListElimNil {motive : RawTerm (scope + 1)} {nilBranch consBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))))
        nilBranch
  /-- `optionMatch motive noneBranch someBranch optionNone ↝ noneBranch`.
      Phase-Z motive shape: motive first (under one binder), scrutinee last;
      the base-case iota discards the motive operationally. -/
  | iotaOptionMatchNone {motive : RawTerm (scope + 1)}
      {noneBranch someBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons (.mkGen .gen_optionNone () .childNil) .childNil)))))
        noneBranch
  /-- `optionMatch motive noneBranch someBranch (optionSome value) ↝ app someBranch value`.
      Phase-Z motive shape; the motive is discarded by the iota. -/
  | iotaOptionMatchSome {motive : RawTerm (scope + 1)}
      {value noneBranch someBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons (.mkGen .gen_optionSome () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)))
  /-- `eitherMatch motive leftBranch rightBranch (eitherInl value) ↝ app leftBranch value`.
      Phase-Z motive shape; the motive is discarded by the iota. -/
  | iotaEitherMatchInl {motive : RawTerm (scope + 1)}
      {value leftBranch rightBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons (.mkGen .gen_eitherInl () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)))
  /-- `eitherMatch motive leftBranch rightBranch (eitherInr value) ↝ app rightBranch value`.
      Phase-Z motive shape; the motive is discarded by the iota. -/
  | iotaEitherMatchInr {motive : RawTerm (scope + 1)}
      {value leftBranch rightBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons (.mkGen .gen_eitherInr () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)))
  /-- `natElim motive z s (natSucc predecessor)
        ↝ s[var 0 := natElim motive z s predecessor, var 1 := predecessor]`.
      Phase-Z motive shape: the SUBSTITUTING succ-iota replaces the
      inductive-hypothesis variable `var 0` with the recursive call
      (threading the same motive/branches) and `var 1` with the
      predecessor. -/
  | iotaNatElimSucc {motive : RawTerm (scope + 1)}
      {predecessor zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaHeadStep
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil)))))
        (RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natElim ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch)
  /-- `natRec motive z s (natSucc predecessor)
        ↝ s[var 0 := natRec motive z s predecessor, var 1 := predecessor]`. -/
  | iotaNatRecSucc {motive : RawTerm (scope + 1)}
      {predecessor zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaHeadStep
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil)))))
        (RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natRec ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch)
  /-- `listElim motive n c (listCons headVal tailVal)
        ↝ app (app (app c headVal) tailVal) (listElim motive n c tailVal)`.
      Phase-Z motive shape: motive first (under one binder), scrutinee last;
      the step-case recursive call REBUILDS a `listElim` spine and THREADS the
      same motive through (eliminating the tail at the same motive). -/
  | iotaListElimCons {motive : RawTerm (scope + 1)}
      {headVal tailVal nilBranch consBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons
                  (.mkGen .gen_listCons ()
                    (.childCons headVal (.childCons tailVal .childNil)))
                  .childNil)))))
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil)))
            (.childCons
              (.mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch
                    (.childCons consBranch (.childCons tailVal .childNil)))))
              .childNil)))
  /-- `idJ motive baseCase (refl rawWitness) ↝ baseCase`.
      Phase-Z motive shape: motive first (under two binders), witness last;
      the base-case iota discards the motive operationally. -/
  | iotaIdJRefl {motive : RawTerm (scope + 2)} {baseCase rawWitness : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_idJ ()
          (.childCons motive
            (.childCons baseCase
              (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))))
        baseCase
  /-- `idStrictRec motive baseCase (refl rawWitness) ↝ baseCase`. -/
  | iotaIdStrictRecRefl {motive : RawTerm (scope + 2)} {baseCase rawWitness : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_idStrictRec ()
          (.childCons motive
            (.childCons baseCase
              (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))))
        baseCase

/-- **Root-iota reduction is deterministic**: an eliminator-headed code has at most one root-iota reduct.
`cases` on both derivations; the diagonal pairs close by `rfl`, and every off-diagonal pair is impossible
(distinct root generators, or — within one eliminator — distinct scrutinee constructors) and is discharged
by index unification. -/
theorem IotaHeadStep.deterministic {scope : Nat} {term firstReduct secondReduct : RawTerm scope}
    (firstStep : IotaHeadStep term firstReduct) (secondStep : IotaHeadStep term secondReduct) :
    firstReduct = secondReduct := by
  cases firstStep <;> cases secondStep <;> rfl

/-- **Root-iota reduction embeds into full reduction.**  Each `IotaHeadStep` rule is the corresponding
`Step` ι constructor at the root.  Through this embedding `IotaHeadStep` inherits subject reduction,
strong-normalization accessibility, and every `Step`-closure property. -/
theorem IotaHeadStep.toStep {scope : Nat} {term reduct : RawTerm scope}
    (iotaStep : IotaHeadStep term reduct) : Step term reduct := by
  cases iotaStep with
  | iotaBoolTrue => exact Step.iotaBoolTrue
  | iotaBoolFalse => exact Step.iotaBoolFalse
  | iotaFstPair => exact Step.iotaFstPair
  | iotaSndPair => exact Step.iotaSndPair
  | iotaNatElimZero => exact Step.iotaNatElimZero
  | iotaNatRecZero => exact Step.iotaNatRecZero
  | iotaListElimNil => exact Step.iotaListElimNil
  | iotaOptionMatchNone => exact Step.iotaOptionMatchNone
  | iotaOptionMatchSome => exact Step.iotaOptionMatchSome
  | iotaEitherMatchInl => exact Step.iotaEitherMatchInl
  | iotaEitherMatchInr => exact Step.iotaEitherMatchInr
  | iotaNatElimSucc => exact Step.iotaNatElimSucc
  | iotaNatRecSucc => exact Step.iotaNatRecSucc
  | iotaListElimCons => exact Step.iotaListElimCons
  | iotaIdJRefl => exact Step.iotaIdJRefl
  | iotaIdStrictRecRefl => exact Step.iotaIdStrictRecRefl

end FX1Poly.Core
