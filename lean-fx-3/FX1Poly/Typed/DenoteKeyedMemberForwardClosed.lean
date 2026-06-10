import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedMemberForwardClosed
    — member-level CR2 (forward closure under `Step`) for the denote relation, UNCONDITIONAL

The first piece of the bounded-CR decomposition (toward B1', the denote member-strong-normalization / lambda-arm
prerequisite).  Of the three reducibility-candidate properties (CR1 member-SN, CR2 forward closure, CR3
neutral-expansion), **CR2 is the one that needs no level bound**: it uses only the `lowerForwardStep` interface
leg (unconditional for `denoteBelowFamily`), never the bounded `neutralInclusion`.  Concretely, every
denote-reducible type's candidate is closed under `Step` on its members.

The proof inducts over `ReducibleTypeStepDenote`:
  * `neutral` (candidate `IsStronglyNormalizing`) — SN is forward-closed (`Acc` inversion), via
    `isStronglyNormalizing_isReducibilityCandidate.closedUnderStep`;
  * `piType` (dependent-arrow candidate) — reduces to the CODOMAIN's CR2 (the inductive hypothesis) composed
    with the function-child congruence `Step.cong .gen_app () (StepChildren.here …)`; the DOMAIN's candidacy is
    NOT used, so no domain CR1/CR3 (hence no bound) is needed;
  * `universeCode` (candidate `SN ∧ ∃ c, lowerAt (denote levelExpr env) · c`) — SN forward-closure on the first
    conjunct, `lowerForwardStep (denote levelExpr env)` on the second;
  * `whnfExpand` / `ofPointwiseIff` — reuse the inductive hypothesis (the latter transporting across the
    pointwise equivalence both ways).

This isolates the level bound entirely to CR1's Π-arm (which needs a domain inhabitant via the bounded
neutral-inclusion) and CR3 — leaving CR2 as a clean unconditional building block the eventual bounded
`isReducibilityCandidate` and the lambda arm's member weak-head expansion will both cite.

## Zero-axiom verification

A structural induction with anonymous-constructor / `match` witnesses per arm; the congruence Step and the SN
forward-closure are by-construction.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-level CR2 (forward closure) for the denote relation, unconditional.**  Given the `lowerForwardStep`
leg (unconditional for `denoteBelowFamily`), every denote-reducible type's candidate is closed under `Step` on
its members.  Inducts over the five `ReducibleTypeStepDenote` arms; the Π arm reduces to the codomain's CR2
(no domain candidacy, hence no level bound), and the universe arm uses only `lowerForwardStep`. -/
theorem ReducibleTypeStepDenote.memberForwardClosed {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerForwardStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm scope}
        {candidate : RawTerm scope → Prop},
      lowerAt lvl typeCode candidate → Step typeCode reduct → lowerAt lvl reduct candidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {term reduct : RawTerm scope}, candidate term → Step term reduct → candidate reduct := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty _notFlat =>
      intro term reduct memberStronglyNormalizing step
      exact isStronglyNormalizing_isReducibilityCandidate.closedUnderStep memberStronglyNormalizing step
  | @piType domainCode codomainCode domainCandidate codomainCandidate _domainReducible
      _codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro function functionAfter functionMember functionStep argument argumentInDomain
      exact codomainInductiveHypothesis argument argumentInDomain
        (functionMember argument argumentInDomain)
        (Step.cong .gen_app ()
          (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep))
  | universeCode levelExpr _flag =>
      intro term reduct member step
      exact ⟨isStronglyNormalizing_isReducibilityCandidate.closedUnderStep member.1 step,
        match member.2 with
        | ⟨lowerCandidate, lowerMember⟩ =>
            ⟨lowerCandidate, lowerForwardStep (LevelExpr.denote levelExpr env) lowerMember step⟩⟩
  | dataEmpty =>
      intro term reduct member step
      exact emptyTaitCandidate.closedUnderStep member step
  | dataFlat _flatPinned =>
      intro term reduct member step
      exact dataTaitCandidate.closedUnderStep member step
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro term reduct member step
      exact (pointwiseIff reduct).mp
        (innerInductiveHypothesis ((pointwiseIff term).mpr member) step)

end FX1Poly.Typed
