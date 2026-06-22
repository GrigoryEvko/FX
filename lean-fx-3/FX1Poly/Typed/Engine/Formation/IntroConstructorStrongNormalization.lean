import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescSubjectStronglyNormalizing
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/IntroConstructorStrongNormalization
    — the INTRO-table twins of the cascade-free step-inversion + SN driver
      (the `introRuleOf` analogues of `formerCellStepIsChildCongruence` /
      `formerCellStronglyNormalizingOfChildren`)

The data/binder INTRODUCERS (`boolTrue` … `refl`, including `lam` / `pathLam`) carry an `introRuleOf` row but
NO formation-table row.  Their VALUE cells are SN once their children are: an introducer is never the HEAD of
a root redex — a constructor appears in a redex only as the SUBJECT (scrutinee/argument), whose redex is headed
by an ELIMINATOR.  And `Step` itself carries no eta (eta is the separate `Step.eta` sibling), so every `Step`
out of an introducer cell is a child congruence, EXACTLY as for the formation formers.

This file ships the introducer twins of the cascade-free SN engine, keyed on `introRuleOf`.
`introConstructorNoWeakHeadStep` is the introducer weak-head-rigidity (the term-indexed-twin
`termIndexedFormationGenerator_noWeakHeadStep` analogue): a `WeakHeadStep` out of an introducer cell would pin
its head to a redex generator (`gen_app` or an eliminator) whose `introRuleOf` is the permanent `none`,
contradicting the introducer classification.  `introConstructorStepInversion` then routes through the
table-free root dispatcher `Step.weakHeadOrChildCong` (no `tableValue : Type` constraint — `IntroRule` lives a
universe above the generic `Step.childCongruenceOfElimHeadsExcluded`'s `tableValue`, so the dispatcher +
rigidity composition is the universe-robust route), and `introConstructorCellStronglyNormalizingOfChildren`
through `formerCell_isStronglyNormalizing_of_accChildren`.  The value-side counterpart used by the
introFundamental rows (TYTAB-4 step 4) whose output type is SN-neutral (Σ / list / option / Id / bridge / nat —
every introducer except the carrier-aware product/either pair).

## Zero-axiom verification

A `cases` over the weak-head-step constructors, each pinning the head to a redex generator whose `introRuleOf`
is the permanent `none` (rigidity); `Step.weakHeadOrChildCong` + rigidity (step inversion);
`formerCell_isStronglyNormalizing_of_accChildren` + `accStepChildrenSuccessor_of_allStronglyNormalizing` (SN
driver).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **An introducer cell admits no weak-head step.**  The introducer twin of
`termIndexedFormationGenerator_noWeakHeadStep`: an introducer (`introRuleOf generator = some rule`) is a
constructor, not an eliminable/applicable head — so the only weak-head arms whose subject unifies pin the head
to a redex generator (`gen_app` or an eliminator) whose `introRuleOf` is the permanent `none`, contradicting
`isIntro`.  The weak-head-rigidity the step inversion consumes. -/
theorem introConstructorNoWeakHeadStep {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : IntroRule} (isIntro : introRuleOf generator = some rule) :
    ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (.mkGen generator payload children) reduct := by
  intro _reduct weakHeadStep
  cases weakHeadStep with
  | beta => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | appCongruence _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | rootIota iotaStep =>
      cases iotaStep <;> nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeBoolElim _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeFst _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeSnd _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeNatElim _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeNatRec _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeListElim _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeOptionMatch _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeEitherMatch _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeIdJ _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeIdStrictRec _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | pathBeta _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | quotRecMk _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | quotElimMk _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | truncRecIntro _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | pathAppCongruence _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeQuotRec _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeQuotElim _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeTruncRec _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | gelBeta _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)
  | scrutineeUngel _ => nomatch (show (none : Option IntroRule) = some rule from isIntro)

/-- **Introducer step inversion.**  A step out of any cell whose head carries an INTRODUCER rule
(`introRuleOf generator = some rule`) is a child congruence: the table-free root dispatcher
`Step.weakHeadOrChildCong` splits into a weak-head step (refuted by `introConstructorNoWeakHeadStep`) or the
child congruence.  Universe-robust (no `tableValue : Type` constraint), so it applies to `IntroRule` despite it
living a universe above the generic `Step.childCongruenceOfElimHeadsExcluded`'s `tableValue`. -/
theorem introConstructorStepInversion {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : IntroRule} {target : RawTerm scope}
    (isIntro : introRuleOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  rcases step.weakHeadOrChildCong with weakHead | childCongruence
  · exact absurd weakHead (introConstructorNoWeakHeadStep isIntro _)
  · exact childCongruence

/-- **An introducer cell with all children strongly normalizing is strongly normalizing.**  CASCADE-FREE generic
assembly (the introducer twin of `formerCellStronglyNormalizingOfChildren`): an introducer heads no root redex
(`introConstructorStepInversion`), so every Step out of the cell is a child congruence; the cell is therefore SN
once its child spine is accessible, which all-children-SN supplies via
`accStepChildrenSuccessor_of_allStronglyNormalizing`.  The value-SN engine the SN-neutral introFundamental rows
consume. -/
theorem introConstructorCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : IntroRule}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isIntro : introRuleOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => introConstructorStepInversion isIntro cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

end FX1Poly.Typed
