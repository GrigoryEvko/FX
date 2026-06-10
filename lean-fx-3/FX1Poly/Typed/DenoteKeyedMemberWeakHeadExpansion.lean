import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedMemberWeakHeadExpansion
    — the member weak-head expansion induction backbone (lambda-arm engine, toward SN-043/#672)

The fundamental theorem's lambda (Π-introduction) arm needs: a β-redex `app (lam body) arg` is a member of a
denote-reducible type's candidate whenever its contractum `subst0 body arg` is (the body's reducibility
supplies exactly that contractum membership).  The general engine is backward closure of any denote-reducible
candidate under a `WeakHeadStep` (with an `IsStronglyNormalizing source` guard) — the β redex is the
`WeakHeadStep.beta` instance, applied at `source = app (lam body) arg` whose SN is
`appLam_isStronglyNormalizing_of_contractum` (`BetaRedexStrongNormalization`).

This file ships the **inductive backbone** `ReducibleTypeStepDenote.memberWeakHeadExpansionModuloPi`: one
induction over `ReducibleTypeStepDenote` discharging FOUR of the five arms intrinsically, with the fifth
(`piType`) isolated as an explicit `piArm` hypothesis — exactly the `ofReducibleTypeStepDenote` discipline
(`DenoteKeyedLevelIrrelevance`).  The general `WeakHeadStep source reduct` + `SN source` formulation is forced:
the β-specific `(body, arg)`-formulation breaks at the Π arm, because the goal there is membership of
`app (app (lam body) arg) a` whose head is a β-redex but which is NOT itself of the form `app (lam body') arg'`,
so a same-redex IH cannot apply; the general form's codomain IH applies to the function-congruence-of-β step
`app source a ↝ app reduct a` (`WeakHeadStep.appCongruence`).

  * `neutral` (candidate `IsStronglyNormalizing`) — `SN source` IS the goal, supplied directly by the guard;
  * `universeCode` (candidate `SN ∧ ∃ c, lowerAt (denote e) · c`) — SN conjunct from the guard, lower conjunct
    via the supplied `lowerBackwardWeakHeadStep` leg on the `WeakHeadStep` (discharged unconditionally for
    `denoteBelowFamily` by `denoteBelowFamily_backwardWeakHeadStep`);
  * `whnfExpand` — the inductive hypothesis (same candidate);
  * `ofPointwiseIff` — the inner inductive hypothesis transported across the pointwise equivalence both ways;
  * `piType` — the supplied `piArm` (the genuinely-hard arm: it must establish `SN (app source a)` — the
    application-SN spine — and compose it with the codomain IH; isolated here, discharged in a later step).

So a proof of the `piArm` alone completes the full member weak-head expansion; the lambda FT arm then
instantiates the backbone with `source = app (lam body) arg`.

## Zero-axiom verification

One `induction` on `ReducibleTypeStepDenote` with the level-independent member-WHE motive; the `universeCode`
arm reassembles via the anonymous constructor (no `funext`); the `ofPointwiseIff` arm transports through the
pointwise iff pointwise (no `funext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member weak-head expansion backbone (modulo the Π arm).**  Backward closure of any denote-reducible
candidate under a `WeakHeadStep` with an `IsStronglyNormalizing source` guard, by induction on the derivation:
`neutral`/`universeCode`/`whnfExpand`/`ofPointwiseIff` discharged intrinsically, `piType` supplied as `piArm`.
The `piArm` hypothesis mirrors the `piType` constructor's data (domain/codomain reducibility + the domain and
per-argument codomain member-WHE inductive hypotheses) and concludes the arrow candidate's member WHE. -/
theorem ReducibleTypeStepDenote.memberWeakHeadExpansionModuloPi {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerBackwardWeakHeadStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm scope}
        {candidate : RawTerm scope → Prop},
      lowerAt lvl reduct candidate → WeakHeadStep typeCode reduct → lowerAt lvl typeCode candidate)
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        (∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
          domainCandidate reduct → domainCandidate source) →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
            codomainCandidate argument reduct → codomainCandidate argument source) →
        ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
          (∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil)))) →
          ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons source (.childCons argument .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
      candidate reduct → candidate source := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty _notFlat =>
      intro source _reduct _weakHeadStep sourceStronglyNormalizing _member
      exact sourceStronglyNormalizing
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis weakHeadStep sourceStronglyNormalizing member
  | universeCode levelExpr _flag =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact ⟨sourceStronglyNormalizing,
        match member.2 with
        | ⟨lowerCandidate, lowerMember⟩ =>
            ⟨lowerCandidate,
              lowerBackwardWeakHeadStep (LevelExpr.denote levelExpr env) lowerMember weakHeadStep⟩⟩
  | dataEmpty =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact emptyTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing member
  | dataFlat _flatPinned =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing member
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact (pointwiseIff source).mp
        (innerInductiveHypothesis weakHeadStep sourceStronglyNormalizing ((pointwiseIff reduct).mpr member))

end FX1Poly.Typed
