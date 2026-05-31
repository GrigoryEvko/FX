import FX1Poly.Core.WhnfInterpretation
import FX1Poly.Core.CandidateInterpretationHeadExpansion

/-! # Foundation/PolyCell/Core/WhnfInterpretationHeadExpansion
    — every weak-head-interpreted type is head-expansion-closed

Alongside `InterpretsWhnf.isReducibilityCandidate`, the fundamental theorem's Π-introduction case
needs each interpreted candidate to be **head-expansion-closed**: a β-redex `app (lam body) argument`
inherits codomain membership from its contractum `subst0 body argument` exactly when the codomain
candidate is closed under head expansion.  This file proves it for the weak-head interpretation, by
induction discharging to the shipped closures.

The two strong-normalization arms (`baseNormal`, `neutralApp`) are both closed by
`isStronglyNormalizing_headExpansionClosed`; the arrow arm by `isArrowReducible_headExpansionClosed`
(the codomain environment kept closed by `isHeadExpansionClosedEnv_cons` from the domain closure); and
`headExpand` forwards its induction hypothesis unchanged (the candidate is the SAME predicate as the
contractum's).  No inhabitedness witness is needed, so this holds at EVERY target scope (the
`IsHeadExpansionClosedEnv` / `isHeadExpansionClosedEnv_cons` machinery is reused verbatim from
`CandidateInterpretationHeadExpansion`).

## Zero-axiom verification

Induction on the interpretation discharging to the shipped closure combinators; the `headExpand` arm
forwards the IH.  `HeadExpansionClosed` is a Pi-type def, so `exact` eta-expands it and the cons
reduction stalls — handled by `refine` (Π arm) as in `CandidateInterpretationHeadExpansion`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Every weak-head-interpreted type-code is head-expansion-closed**, given a head-expansion-closed
environment.  Induction on the interpretation: a type variable's candidate comes from the environment;
the SN candidate (`baseNormal` / `neutralApp`) is closed by `isStronglyNormalizing_headExpansionClosed`;
the arrow candidate by `isArrowReducible_headExpansionClosed`; and `headExpand` forwards its induction
hypothesis (the candidate is unchanged). -/
theorem InterpretsWhnf.headExpansionClosed {scope targetScope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate : RawTerm targetScope → Prop}
    (interprets : InterpretsWhnf env typeCode candidate) :
    IsHeadExpansionClosedEnv env → HeadExpansionClosed candidate := by
  induction interprets with
  | typeVariable environment index =>
      intro envClosed
      exact envClosed index
  | piType _domainInterprets _codomainInterprets domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro envClosed
      refine isArrowReducible_headExpansionClosed ?_
      exact codomainInductiveHypothesis
        (isHeadExpansionClosedEnv_cons (domainInductiveHypothesis envClosed) envClosed)
  | baseNormal environment _notVariable _notPiType _notApp =>
      intro _envClosed
      exact isStronglyNormalizing_headExpansionClosed
  | neutralApp environment _noHeadStep =>
      intro _envClosed
      exact isStronglyNormalizing_headExpansionClosed
  | headExpand _headStep _reductInterprets reductInductiveHypothesis =>
      intro envClosed
      exact reductInductiveHypothesis envClosed

end FX1Poly.Core
