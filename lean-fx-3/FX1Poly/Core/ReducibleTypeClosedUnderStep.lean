import FX1Poly.Core.ReducibleType
import FX1Poly.Core.ReducibilityCandidate

/-! # Foundation/PolyCell/Core/ReducibleTypeClosedUnderStep
    — CR2 for every dependent-reducible candidate (forward step-closure)

The full reducibility-candidate property `IsReducibilityCandidate` (`ReducibilityCandidate.lean`) has
three conditions — CR1 (members are SN), CR2 (closed forward under `Step`), CR3 (neutral expansion).
This file establishes **CR2 for every candidate `ReducibleType` assigns**, uniformly, by induction on
the derivation.  Unlike CR3 — whose dependent-arrow case is the conversion-invariance wall (it needs
the codomain candidate stable under ARGUMENT reduction; see `ReducibleTypeArrowCandidate.lean`) — CR2
goes through unconditionally: the Π case needs only the codomain candidate's *own* CR2 from the
induction hypothesis, not full candidate-hood.

Arms:
  * `headExpand` — the candidate is literally the contractum's, so its CR2 is the induction hypothesis;
  * `neutral` — the candidate is `IsStronglyNormalizing`, whose CR2 is one-step `Acc`-inversion
    (`isStronglyNormalizing_isReducibilityCandidate.closedUnderStep`);
  * `piType` — a function-position step `functionTerm ↝ functionReduct` lifts to the application step
    `app functionTerm argument ↝ app functionReduct argument` (`Step.cong gen_app` / `StepChildren.here`),
    and the codomain candidate's CR2 (the induction hypothesis at each reducible argument) carries
    dependent-arrow membership across.

This is the unconditional half of `ReducibleType.isReducibilityCandidate` (CR1 + CR3 route through the
arrow's domain-witness / conversion-invariance; CR2 does not), and a standalone ingredient the
fundamental theorem and the eventual candidate-hood assembly consume.

## Zero-axiom verification

Induction on `ReducibleType` + the shipped SN CR2 + `Step.cong`/`StepChildren.here` congruence.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **CR2 for every dependent-reducible candidate.**  The candidate `ReducibleType` assigns to a
type-code is closed forward under one `Step`.  Proved by induction: `headExpand` forwards the
contractum's CR2; `neutral`'s SN candidate is closed by `Acc`-inversion; the dependent arrow lifts a
function step to an application step and the codomain candidate's CR2 carries membership across. -/
theorem ReducibleType.candidateClosedUnderStep {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    ∀ {term reduct : RawTerm scope}, candidate term → Step term reduct → candidate reduct := by
  induction reducible with
  | headExpand _headStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | iotaExpand _iotaStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noHeadStep _noIotaHeadStep _notPiType =>
      intro term reduct stronglyNormalizingTerm stepTermReduct
      exact isStronglyNormalizing_isReducibilityCandidate.closedUnderStep
        stronglyNormalizingTerm stepTermReduct
  | piType _codomainCandidate _domainReducible _codomainReducible
      _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro functionTerm functionReduct candidateFunctionTerm stepFunction
      intro argument argumentReducible
      have membershipAtFunction := candidateFunctionTerm argument argumentReducible
      have stepApplication :
          Step
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
            (.mkGen .gen_app () (.childCons functionReduct (.childCons argument .childNil))) :=
        Step.cong .gen_app ()
          (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) stepFunction)
      exact codomainInductiveHypothesis argument argumentReducible
        membershipAtFunction stepApplication

end FX1Poly.Core
