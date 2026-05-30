import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StrongNormalizationSubterm
    — strong normalization of sub-terms (the inverse of the constructor lane)

The constructor file proves children SN ⟹ parent SN (the forward direction).
This file proves the INVERSE for the first pair component: the first component
of a strongly-normalizing pair is itself strongly normalizing.  Every
payload-carrying eliminator's ι-rule extracts a sub-term or payload from the
scrutinee (`fst (pair a b) ↝ a`, `optionMatch … (Some v) ↝ app branch v`,
…), so its SN closure needs the extracted sub-term's SN — which this primitive
supplies from the scrutinee's accessibility.  (The second-component sibling
follows the same shape with a `there`-then-`here` congruence and lands next.)

## The argument

A first-component step lifts to a pair step by congruence
(`Step.cong .gen_pair () (StepChildren.here …)`).  So every reduction
sequence out of the component embeds into one out of the pair, and the pair's
accessibility transfers to the component.  The proof is an `Acc` induction on
the pair's accessibility — generalized over the pair term as a variable so the
recursion's index is a variable (Lean cannot recurse structurally on a
compound `Acc` index directly).

## Zero-axiom verification

`Acc` induction + the `Step.cong` congruence lift.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`.  Covered by the
`#audit_namespace FX1Poly.Core` sweep in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- The first component of a strongly-normalizing pair is strongly
normalizing.  Each first-component step lifts to a pair step via the head
congruence (`StepChildren.here`); the `Acc` induction is generalized over the
pair term so the recursion's index is a variable. -/
theorem firstComponent_isStronglyNormalizing_of_pair {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (pairTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing firstValue := by
  suffices general :
      ∀ {pairTerm : RawTerm scope}, Acc StepSuccessor pairTerm →
        ∀ {currentFirst currentSecond : RawTerm scope},
          pairTerm = .mkGen .gen_pair ()
            (.childCons currentFirst (.childCons currentSecond .childNil)) →
          Acc StepSuccessor currentFirst from
    general pairTerminates rfl
  intro pairTerm pairAccessible
  induction pairAccessible with
  | intro pairWitness _pairPredecessors pairInductiveHypothesis =>
      intro currentFirst currentSecond witnessEq
      subst witnessEq
      apply Acc.intro
      intro firstAfter firstStep
      have congruenceLift :
          Step
            (.mkGen .gen_pair ()
              (.childCons currentFirst (.childCons currentSecond .childNil)) :
              RawTerm scope)
            (.mkGen .gen_pair ()
              (.childCons firstAfter (.childCons currentSecond .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_pair ()
          (StepChildren.here
            (.childCons currentSecond .childNil :
              RawTermChildren [0] scope)
            firstStep)
      exact pairInductiveHypothesis
        (.mkGen .gen_pair ()
          (.childCons firstAfter (.childCons currentSecond .childNil)))
        congruenceLift rfl

end StepStar
end FX1Poly.Core
