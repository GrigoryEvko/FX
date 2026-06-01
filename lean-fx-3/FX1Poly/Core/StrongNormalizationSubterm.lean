import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StrongNormalizationSubterm
    — strong normalization of sub-terms (the inverse of the constructor direction)

The constructor file proves children SN ⟹ parent SN (the forward direction).
This file proves the INVERSE for the first pair component: the first component
of a strongly-normalizing pair is itself strongly normalizing.  Every
payload-carrying eliminator's ι-rule extracts a sub-term or payload from the
scrutinee (`fst (pair a b) ↝ a`, `optionMatch … (Some v) ↝ app branch v`,
…), so its SN closure needs the extracted sub-term's SN — which this primitive
supplies from the scrutinee's accessibility.  (The second-component sibling
follows the same shape with a `there`-then-`here` congruence.)

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

/-- The second component of a strongly-normalizing pair is strongly
normalizing.  Symmetric to the first via the tail-then-head congruence
(`StepChildren.there … StepChildren.here`).  The `there` head's binder shift is
pinned with the explicit `@`-form because `gen_pair.binderShifts = [0, 0]` does
not auto-reduce for the elaborator. -/
theorem secondComponent_isStronglyNormalizing_of_pair {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (pairTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing secondValue := by
  suffices general :
      ∀ {pairTerm : RawTerm scope}, Acc StepSuccessor pairTerm →
        ∀ {currentFirst currentSecond : RawTerm scope},
          pairTerm = .mkGen .gen_pair ()
            (.childCons currentFirst (.childCons currentSecond .childNil)) →
          Acc StepSuccessor currentSecond from
    general pairTerminates rfl
  intro pairTerm pairAccessible
  induction pairAccessible with
  | intro pairWitness _pairPredecessors pairInductiveHypothesis =>
      intro currentFirst currentSecond witnessEq
      subst witnessEq
      apply Acc.intro
      intro secondAfter secondStep
      have congruenceLift :
          Step
            (.mkGen .gen_pair ()
              (.childCons currentFirst (.childCons currentSecond .childNil)) :
              RawTerm scope)
            (.mkGen .gen_pair ()
              (.childCons currentFirst (.childCons secondAfter .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_pair ()
          (@StepChildren.there scope 0 [0] currentFirst _ _
            (StepChildren.here
              (.childNil : RawTermChildren [] scope) secondStep))
      exact pairInductiveHypothesis
        (.mkGen .gen_pair ()
          (.childCons currentFirst (.childCons secondAfter .childNil)))
        congruenceLift rfl

/-- The function head of a strongly-normalizing application is strongly
normalizing.  `gen_app` has the same `[0, 0]` two-child shape as `gen_pair`, so
this is the head-congruence mirror of
`firstComponent_isStronglyNormalizing_of_pair`: each head step lifts to an
application step via `StepChildren.here`, so the application's accessibility
transfers to the head.  This is the inverse the arrow reducibility candidate's
CR1 turns on — `SN (app f x)` (from the codomain candidate) descends to
`SN f`. -/
theorem appHead_isStronglyNormalizing_of_app {scope : Nat}
    {functionTerm argumentTerm : RawTerm scope}
    (applicationTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_app ()
          (.childCons functionTerm (.childCons argumentTerm .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing functionTerm := by
  suffices general :
      ∀ {applicationTerm : RawTerm scope},
        Acc StepSuccessor applicationTerm →
          ∀ {currentFunction currentArgument : RawTerm scope},
            applicationTerm = .mkGen .gen_app ()
              (.childCons currentFunction
                (.childCons currentArgument .childNil)) →
            Acc StepSuccessor currentFunction from
    general applicationTerminates rfl
  intro applicationTerm applicationAccessible
  induction applicationAccessible with
  | intro applicationWitness _applicationPredecessors
      applicationInductiveHypothesis =>
      intro currentFunction currentArgument witnessEq
      subst witnessEq
      apply Acc.intro
      intro functionAfter functionStep
      have congruenceLift :
          Step
            (.mkGen .gen_app ()
              (.childCons currentFunction
                (.childCons currentArgument .childNil)) :
              RawTerm scope)
            (.mkGen .gen_app ()
              (.childCons functionAfter
                (.childCons currentArgument .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_app ()
          (StepChildren.here
            (.childCons currentArgument .childNil :
              RawTermChildren [0] scope)
            functionStep)
      exact applicationInductiveHypothesis
        (.mkGen .gen_app ()
          (.childCons functionAfter (.childCons currentArgument .childNil)))
        congruenceLift rfl

/-- The argument of a strongly-normalizing application is strongly normalizing.
The argument-congruence sibling of `appHead_isStronglyNormalizing_of_app`,
mirroring `secondComponent_isStronglyNormalizing_of_pair`: each argument step
lifts via the tail-then-head congruence (`StepChildren.there … here`), with the
`there` head's binder shift pinned by the explicit `@`-form because
`gen_app.binderShifts = [0, 0]` does not auto-reduce. -/
theorem appArgument_isStronglyNormalizing_of_app {scope : Nat}
    {functionTerm argumentTerm : RawTerm scope}
    (applicationTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_app ()
          (.childCons functionTerm (.childCons argumentTerm .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing argumentTerm := by
  suffices general :
      ∀ {applicationTerm : RawTerm scope},
        Acc StepSuccessor applicationTerm →
          ∀ {currentFunction currentArgument : RawTerm scope},
            applicationTerm = .mkGen .gen_app ()
              (.childCons currentFunction
                (.childCons currentArgument .childNil)) →
            Acc StepSuccessor currentArgument from
    general applicationTerminates rfl
  intro applicationTerm applicationAccessible
  induction applicationAccessible with
  | intro applicationWitness _applicationPredecessors
      applicationInductiveHypothesis =>
      intro currentFunction currentArgument witnessEq
      subst witnessEq
      apply Acc.intro
      intro argumentAfter argumentStep
      have congruenceLift :
          Step
            (.mkGen .gen_app ()
              (.childCons currentFunction
                (.childCons currentArgument .childNil)) :
              RawTerm scope)
            (.mkGen .gen_app ()
              (.childCons currentFunction
                (.childCons argumentAfter .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_app ()
          (@StepChildren.there scope 0 [0] currentFunction _ _
            (StepChildren.here
              (.childNil : RawTermChildren [] scope) argumentStep))
      exact applicationInductiveHypothesis
        (.mkGen .gen_app ()
          (.childCons currentFunction (.childCons argumentAfter .childNil)))
        congruenceLift rfl

/-- The domain child of a strongly-normalizing Pi type code is strongly normalizing.
Every domain step lifts to a congruence step under the `gen_piTyCode` cell, so accessibility of the parent
transfers to the first child. -/
theorem domain_isStronglyNormalizing_of_piTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (piTypeCodeTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing domainCode := by
  suffices general :
      ∀ {piTypeCode : RawTerm scope}, Acc StepSuccessor piTypeCode →
        ∀ {currentDomain : RawTerm scope} {currentCodomain : RawTerm (scope + 1)},
          piTypeCode = .mkGen .gen_piTyCode ()
            (.childCons currentDomain (.childCons currentCodomain .childNil)) →
          Acc StepSuccessor currentDomain from
    general piTypeCodeTerminates rfl
  intro piTypeCode piTypeCodeAccessible
  induction piTypeCodeAccessible with
  | intro piTypeCodeWitness _piTypeCodePredecessors piTypeCodeInductiveHypothesis =>
      intro currentDomain currentCodomain witnessEq
      subst witnessEq
      apply Acc.intro
      intro domainAfter domainStep
      have congruenceLift :
          Step
            (.mkGen .gen_piTyCode ()
              (.childCons currentDomain (.childCons currentCodomain .childNil)) :
              RawTerm scope)
            (.mkGen .gen_piTyCode ()
              (.childCons domainAfter (.childCons currentCodomain .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_piTyCode ()
          (StepChildren.here
            (.childCons currentCodomain .childNil :
              RawTermChildren [1] scope)
            domainStep)
      exact piTypeCodeInductiveHypothesis
        (.mkGen .gen_piTyCode ()
          (.childCons domainAfter (.childCons currentCodomain .childNil)))
        congruenceLift rfl

/-- The codomain child of a strongly-normalizing Pi type code is strongly normalizing.
The codomain lives under the Pi binder, so the lifted congruence step walks once into the child spine before
firing at the second child. -/
theorem codomain_isStronglyNormalizing_of_piTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (piTypeCodeTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing codomainCode := by
  suffices general :
      ∀ {piTypeCode : RawTerm scope}, Acc StepSuccessor piTypeCode →
        ∀ {currentDomain : RawTerm scope} {currentCodomain : RawTerm (scope + 1)},
          piTypeCode = .mkGen .gen_piTyCode ()
            (.childCons currentDomain (.childCons currentCodomain .childNil)) →
          Acc StepSuccessor currentCodomain from
    general piTypeCodeTerminates rfl
  intro piTypeCode piTypeCodeAccessible
  induction piTypeCodeAccessible with
  | intro piTypeCodeWitness _piTypeCodePredecessors piTypeCodeInductiveHypothesis =>
      intro currentDomain currentCodomain witnessEq
      subst witnessEq
      apply Acc.intro
      intro codomainAfter codomainStep
      have congruenceLift :
          Step
            (.mkGen .gen_piTyCode ()
              (.childCons currentDomain (.childCons currentCodomain .childNil)) :
              RawTerm scope)
            (.mkGen .gen_piTyCode ()
              (.childCons currentDomain (.childCons codomainAfter .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_piTyCode ()
          (@StepChildren.there scope 0 [1] currentDomain _ _
            (StepChildren.here
              (.childNil : RawTermChildren [] scope) codomainStep))
      exact piTypeCodeInductiveHypothesis
        (.mkGen .gen_piTyCode ()
          (.childCons currentDomain (.childCons codomainAfter .childNil)))
        congruenceLift rfl

/-- The domain child of a strongly-normalizing Sigma type code is strongly normalizing. -/
theorem domain_isStronglyNormalizing_of_sigmaTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (sigmaTypeCodeTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_sigmaTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing domainCode := by
  suffices general :
      ∀ {sigmaTypeCode : RawTerm scope}, Acc StepSuccessor sigmaTypeCode →
        ∀ {currentDomain : RawTerm scope} {currentCodomain : RawTerm (scope + 1)},
          sigmaTypeCode = .mkGen .gen_sigmaTyCode ()
            (.childCons currentDomain (.childCons currentCodomain .childNil)) →
          Acc StepSuccessor currentDomain from
    general sigmaTypeCodeTerminates rfl
  intro sigmaTypeCode sigmaTypeCodeAccessible
  induction sigmaTypeCodeAccessible with
  | intro sigmaTypeCodeWitness _sigmaTypeCodePredecessors sigmaTypeCodeInductiveHypothesis =>
      intro currentDomain currentCodomain witnessEq
      subst witnessEq
      apply Acc.intro
      intro domainAfter domainStep
      have congruenceLift :
          Step
            (.mkGen .gen_sigmaTyCode ()
              (.childCons currentDomain (.childCons currentCodomain .childNil)) :
              RawTerm scope)
            (.mkGen .gen_sigmaTyCode ()
              (.childCons domainAfter (.childCons currentCodomain .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_sigmaTyCode ()
          (StepChildren.here
            (.childCons currentCodomain .childNil :
              RawTermChildren [1] scope)
            domainStep)
      exact sigmaTypeCodeInductiveHypothesis
        (.mkGen .gen_sigmaTyCode ()
          (.childCons domainAfter (.childCons currentCodomain .childNil)))
        congruenceLift rfl

/-- The codomain child of a strongly-normalizing Sigma type code is strongly normalizing. -/
theorem codomain_isStronglyNormalizing_of_sigmaTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (sigmaTypeCodeTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_sigmaTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing codomainCode := by
  suffices general :
      ∀ {sigmaTypeCode : RawTerm scope}, Acc StepSuccessor sigmaTypeCode →
        ∀ {currentDomain : RawTerm scope} {currentCodomain : RawTerm (scope + 1)},
          sigmaTypeCode = .mkGen .gen_sigmaTyCode ()
            (.childCons currentDomain (.childCons currentCodomain .childNil)) →
          Acc StepSuccessor currentCodomain from
    general sigmaTypeCodeTerminates rfl
  intro sigmaTypeCode sigmaTypeCodeAccessible
  induction sigmaTypeCodeAccessible with
  | intro sigmaTypeCodeWitness _sigmaTypeCodePredecessors sigmaTypeCodeInductiveHypothesis =>
      intro currentDomain currentCodomain witnessEq
      subst witnessEq
      apply Acc.intro
      intro codomainAfter codomainStep
      have congruenceLift :
          Step
            (.mkGen .gen_sigmaTyCode ()
              (.childCons currentDomain (.childCons currentCodomain .childNil)) :
              RawTerm scope)
            (.mkGen .gen_sigmaTyCode ()
              (.childCons currentDomain (.childCons codomainAfter .childNil)) :
              RawTerm scope) :=
        Step.cong .gen_sigmaTyCode ()
          (@StepChildren.there scope 0 [1] currentDomain _ _
            (StepChildren.here
              (.childNil : RawTermChildren [] scope) codomainStep))
      exact sigmaTypeCodeInductiveHypothesis
        (.mkGen .gen_sigmaTyCode ()
          (.childCons currentDomain (.childCons codomainAfter .childNil)))
        congruenceLift rfl

end StepStar
end FX1Poly.Core
