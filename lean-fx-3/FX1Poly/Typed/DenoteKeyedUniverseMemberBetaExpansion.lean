import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedUniverseMemberBetaExpansion
    — the universe arm of the denote member weak-head β-expansion (lambda-arm engine, toward SN-043/#672)

The denote member weak-head β-expansion is the engine the fundamental theorem's lambda (Π-introduction) arm
will run: a β-redex `app (lam body) arg` is a member of a denote-reducible type's candidate whenever its
contractum `subst0 body arg` is (the lambda body's reducibility supplies exactly that contractum membership).
That engine is one induction over `ReducibleTypeStepDenote` with five arms — neutral, universe, whnfExpand,
ofPointwiseIff, piType.  This file ships the **universe arm** as a standalone, composing the two prior bricks:

  * SN conjunct — `appLam_isStronglyNormalizing_of_contractum` (`BetaRedexStrongNormalization`, the neutral
    arm): `app (lam body) arg` is SN from the binder/argument/single-contractum being SN;
  * `∃ candidate, lowerAt (denote levelExpr env) · candidate` conjunct — the lower family's backward
    weak-head-step leg applied to `WeakHeadStep.beta` (`app (lam body) arg ↝ subst0 body arg`).

It is parametric over the `lowerBackwardWeakHeadStep` leg, which `denoteBelowFamily` discharges UNCONDITIONALLY
(`denoteBelowFamily_backwardWeakHeadStep` — an implication vacuous on the empty above-bound family, never the
bounded existence obligation `lowerNeutralInclusion`).  So the universe arm of the lambda-arm engine is
BOUND-FREE: the level bound is confined to the remaining Π/spine arm (`app (app (lam body) arg) a`, a
function-congruence-of-β step needing the application-SN spine).

## Zero-axiom verification

A single anonymous-constructor term: `⟨appLam_isStronglyNormalizing_of_contractum …, ⟨candidate, leg …⟩⟩`,
flattening the `SN ∧ ∃ candidate, lowerAt …` of `universeDenotePredicate`.  No tactic, no recursion — it
inherits the zero-axiom status of its components and the supplied leg.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Universe arm of the denote member weak-head β-expansion.**  For the denote universe candidate
`universeDenotePredicate env lowerAt levelExpr`, the β-redex `app (lam body) arg` is a member given the
contractum `subst0 body arg` is a member and the binder `lam body` and argument `arg` are SN.  The SN conjunct
is `appLam_isStronglyNormalizing_of_contractum`; the lower-family conjunct transports across the β
`WeakHeadStep` via the supplied backward leg (discharged unconditionally by `denoteBelowFamily_backwardWeakHeadStep`
for the real relation). -/
theorem universeMemberBetaExpansionAtDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (levelExpr : LevelExpr)
    (lowerBackwardWeakHeadStep :
      ∀ {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop},
        lowerAt (LevelExpr.denote levelExpr env) reduct candidate → WeakHeadStep typeCode reduct →
        lowerAt (LevelExpr.denote levelExpr env) typeCode candidate)
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {arg : RawTerm scope}
    (lamStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))))
    (argumentStronglyNormalizing : IsStronglyNormalizing arg)
    (contractumMember : universeDenotePredicate env lowerAt levelExpr (RawTerm.subst0 body arg)) :
    universeDenotePredicate env lowerAt levelExpr
      (applicationCell
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) arg) :=
  ⟨appLam_isStronglyNormalizing_of_contractum lamStronglyNormalizing argumentStronglyNormalizing
      contractumMember.1,
    match contractumMember.2 with
    | ⟨candidate, lowerMember⟩ =>
        ⟨candidate, lowerBackwardWeakHeadStep lowerMember WeakHeadStep.beta⟩⟩

end FX1Poly.Typed
