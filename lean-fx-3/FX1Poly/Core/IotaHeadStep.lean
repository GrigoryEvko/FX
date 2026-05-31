import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/IotaHeadStep
    — deterministic root-iota reduction for eliminator-headed codes

`HeadStep` (`HeadStep.lean`) captures the β half of weak-head reduction: contract the head β-redex, or
head-reduce into the function spine.  This file captures the COMPLEMENTARY ι half: contract the
eliminator-on-constructor redex AT THE ROOT — `boolElim boolTrue t e ↝ t`, `natRec (natSucc p) z s ↝
app (app s p) (natRec p z s)`, etc. — and nothing else (no congruence, no reduction into the
scrutinee).

Why a separate root-only relation (rather than reusing `Step`'s ι constructors): like `HeadStep.beta`,
the point is DETERMINISM.  At a fixed eliminator-headed code with a constructor scrutinee, exactly one ι
rule fires and its contractum is unique — the root generator plus the scrutinee constructor pick the
rule, and the rule's contractum is a function of the redex.  That determinism is what a weak-head-normal
dispatching reducibility relation needs to stay functional once large elimination lets an eliminator
appear AS A TYPE-CODE (`natRec`-at-a-universe, roadmap #435/#436): such a code is NOT `HeadStep`-reducible
(it is `gen_natRec`-rooted, not `gen_app`-rooted) yet it is a genuine root redex, so the
`ReducibleType.neutral` arm (`¬ HeadStep ∧ root ≠ piTyCode → SN`) would mis-classify it.  `IotaHeadStep`
is the substrate the large-elimination-ready `iotaExpand` companion arm will dispatch on, exactly as
`headExpand` dispatches on `HeadStep`.  It is also the reduction characterization the typed ι subject-
reduction (#475/#476), the weak-head normalizer, and the Path-B convergent rewrite presentation consume.

The sixteen rules are the same redex/contractum pairs as `Step`'s ι constructors (§11.6.1 SHAPE 1-5),
restricted to the root: SHAPE 1 branch-selection (bool×2 / nat-zero×2 / list-nil / option-none / idJ-refl
/ idStrictRec-refl), SHAPE 2 content-projection (pair fst/snd), SHAPE 3 1-arg app-chain (option-some /
either-inl/inr), SHAPE 4 2-arg app-chain with recursion (natElim/natRec on succ), SHAPE 5 3-arg app-chain
(listElim on cons).

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
  /-- `boolElim boolTrue thenBranch elseBranch ↝ thenBranch`. -/
  | iotaBoolTrue {thenBranch elseBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_boolElim ()
          (.childCons (.mkGen .gen_boolTrue () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))))
        thenBranch
  /-- `boolElim boolFalse thenBranch elseBranch ↝ elseBranch`. -/
  | iotaBoolFalse {thenBranch elseBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_boolElim ()
          (.childCons (.mkGen .gen_boolFalse () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))))
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
  /-- `natElim natZero zeroBranch succBranch ↝ zeroBranch`. -/
  | iotaNatElimZero {zeroBranch succBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_natElim ()
          (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        zeroBranch
  /-- `natRec natZero zeroBranch succBranch ↝ zeroBranch`. -/
  | iotaNatRecZero {zeroBranch succBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_natRec ()
          (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        zeroBranch
  /-- `listElim listNil nilBranch consBranch ↝ nilBranch`. -/
  | iotaListElimNil {nilBranch consBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_listElim ()
          (.childCons (.mkGen .gen_listNil () .childNil)
            (.childCons nilBranch (.childCons consBranch .childNil))))
        nilBranch
  /-- `optionMatch optionNone noneBranch someBranch ↝ noneBranch`. -/
  | iotaOptionMatchNone {noneBranch someBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons (.mkGen .gen_optionNone () .childNil)
            (.childCons noneBranch (.childCons someBranch .childNil))))
        noneBranch
  /-- `optionMatch (optionSome value) noneBranch someBranch ↝ app someBranch value`. -/
  | iotaOptionMatchSome {value noneBranch someBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons (.mkGen .gen_optionSome () (.childCons value .childNil))
            (.childCons noneBranch (.childCons someBranch .childNil))))
        (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)))
  /-- `eitherMatch (eitherInl value) leftBranch rightBranch ↝ app leftBranch value`. -/
  | iotaEitherMatchInl {value leftBranch rightBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons (.mkGen .gen_eitherInl () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
        (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)))
  /-- `eitherMatch (eitherInr value) leftBranch rightBranch ↝ app rightBranch value`. -/
  | iotaEitherMatchInr {value leftBranch rightBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons (.mkGen .gen_eitherInr () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
        (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)))
  /-- `natElim (natSucc predecessor) z s ↝ app (app s predecessor) (natElim predecessor z s)`. -/
  | iotaNatElimSucc {predecessor zeroBranch succBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_natElim ()
          (.childCons (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natElim ()
                (.childCons predecessor
                  (.childCons zeroBranch (.childCons succBranch .childNil))))
              .childNil)))
  /-- `natRec (natSucc predecessor) z s ↝ app (app s predecessor) (natRec predecessor z s)`. -/
  | iotaNatRecSucc {predecessor zeroBranch succBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_natRec ()
          (.childCons (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natRec ()
                (.childCons predecessor
                  (.childCons zeroBranch (.childCons succBranch .childNil))))
              .childNil)))
  /-- `listElim (listCons headVal tailVal) n c ↝ app (app (app c headVal) tailVal) (listElim tailVal n c)`. -/
  | iotaListElimCons {headVal tailVal nilBranch consBranch : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_listElim ()
          (.childCons
            (.mkGen .gen_listCons ()
              (.childCons headVal (.childCons tailVal .childNil)))
            (.childCons nilBranch (.childCons consBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil)))
            (.childCons
              (.mkGen .gen_listElim ()
                (.childCons tailVal
                  (.childCons nilBranch (.childCons consBranch .childNil))))
              .childNil)))
  /-- `idJ baseCase (refl rawWitness) ↝ baseCase`. -/
  | iotaIdJRefl {baseCase rawWitness : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_idJ ()
          (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil)))
        baseCase
  /-- `idStrictRec baseCase (refl rawWitness) ↝ baseCase`. -/
  | iotaIdStrictRecRefl {baseCase rawWitness : RawTerm scope} :
      IotaHeadStep
        (.mkGen .gen_idStrictRec ()
          (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil)))
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
