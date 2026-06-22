import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescSubjectStronglyNormalizing
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables

/-! # FX1Poly/Typed/FlatFormerStrongNormalization
    — the FLAT-table twins of the cascade-free former step-inversion + SN driver + weak-head-normality
      (the `flatTypingRuleDescOf` analogues of `formerCellStepIsChildCongruence` /
      `formerCellStronglyNormalizingOfChildren` / `formationGenerator_noWeakHeadStep`)

`FormerStepInversionGeneric` ships the cascade-free step-inversion `formerCellStepIsChildCongruence` and
`HasTypeDescSubjectStronglyNormalizing` ships the SN driver `formerCellStronglyNormalizingOfChildren` — BOTH
keyed on the CUMULATIVE table `typingRuleDescOf` (the dependent Π/Σ binders + the element-shape data codes
list/option).  The non-dependent FLAT formers (product / sum / either / arrow / equiv and the cohesion
modalities ʃ / ♭ / ♯) carry NO `typingRuleDescOf` row — they are typed by the union's flat-family arm over
`flatTypingRuleDescOf` — so those cumulative-keyed lemmas do not apply.  This file ships the IDENTICAL
constructions keyed on the flat table, so a flat former's cell is SN once its children are, and heads no
weak-head step.

Every twin routes through the SAME table-generic cores the cumulative versions use — `flatFormerStepInversion`
through `Step.childCongruenceOfElimHeadsExcluded` (two arms, not eighteen), `flatFormerCellStronglyNormalizing`
through `formerCell_isStronglyNormalizing_of_accChildren` (the generic congruence-only-generator accessibility
lift).  The exclusion certificate `legacyElimHead_hasNoFlatFormationRule` is the one cross-table fact: every
operational row's eliminator head carries NO flat formation rule (one `rfl` per row), so a new iota row owes a
single entry and a new flat formation row is absorbed zero-touch.

## Zero-axiom verification

`Step.childCongruenceOfElimHeadsExcluded` + a 17-case `rfl` membership enumeration + `Option.noConfusion`
(step inversion); `formerCell_isStronglyNormalizing_of_accChildren` +
`accStepChildrenSuccessor_of_allStronglyNormalizing` (SN driver); a `cases` over the weak-head-step
constructors, each pinning the head to a redex generator whose `flatTypingRuleDescOf` is the permanent `none`
(weak-head-normality).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **No operational row's eliminator head carries a FLAT formation rule** — the flat-table exclusion
certificate: every operational row's eliminator head (`gen_app` and the data/identity eliminators) is disjoint
from the flat formation table's domain.  One `rfl` per row; a new iota row owes exactly one new entry.  (A
public twin of the `private` copy in `ConvFlatFormerRigidity`; the canonical step-inversion home is here,
alongside the SN driver.) -/
theorem legacyElimHead_hasNoFlatFormationRule :
    ∀ rule : IotaRuleDesc, rule ∈ iotaRuleTable →
      flatTypingRuleDescOf rule.elimGenerator = none := by
  intro rule isRow
  cases isRow with
  | head => rfl
  | tail _ isRow => cases isRow with
    | head => rfl
    | tail _ isRow => cases isRow with
      | head => rfl
      | tail _ isRow => cases isRow with
        | head => rfl
        | tail _ isRow => cases isRow with
          | head => rfl
          | tail _ isRow => cases isRow with
            | head => rfl
            | tail _ isRow => cases isRow with
              | head => rfl
              | tail _ isRow => cases isRow with
                | head => rfl
                | tail _ isRow => cases isRow with
                  | head => rfl
                  | tail _ isRow => cases isRow with
                    | head => rfl
                    | tail _ isRow => cases isRow with
                      | head => rfl
                      | tail _ isRow => cases isRow with
                        | head => rfl
                        | tail _ isRow => cases isRow with
                          | head => rfl
                          | tail _ isRow => cases isRow with
                            | head => rfl
                            | tail _ isRow => cases isRow with
                              | head => rfl
                              | tail _ isRow => cases isRow with
                                | head => rfl
                                | tail _ isRow => cases isRow with
                                  | head => rfl
                                  | tail _ isRow => cases isRow with
                                    | head => rfl
                                    | tail _ isRow => cases isRow with
                                      | head => rfl
                                      | tail _ isRow => cases isRow with
                                        | head => rfl
                                        | tail _ isRow => cases isRow with
                                          | head => rfl
                                          | tail _ isRow => cases isRow with
                                            | head => rfl
                                            | tail _ isRow => cases isRow

/-- **Flat-former step inversion.**  A step out of any cell whose head carries a FLAT formation rule
(`flatTypingRuleDescOf generator = some rule`) is a child congruence — proven without enumerating the flat
formation table (the table-generic `Step.childCongruenceOfElimHeadsExcluded` at the flat exclusion
certificate), so every future flat formation row is absorbed zero-touch. -/
theorem flatFormerStepInversion {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' :=
  Step.childCongruenceOfElimHeadsExcluded
    legacyElimHead_hasNoFlatFormationRule isFlatFormation step

/-- **A flat former cell with all children strongly normalizing is strongly normalizing.**  CASCADE-FREE
generic assembly (the flat twin of `formerCellStronglyNormalizingOfChildren`): a flat formation generator heads
no root redex (`flatFormerStepInversion`), so every Step out of the cell is a child congruence; the cell is
therefore SN once its child spine is accessible, which all-children-SN supplies via
`accStepChildrenSuccessor_of_allStronglyNormalizing`.  A new flat formation row extends it with no change to
this proof. -/
theorem flatFormerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TypingRuleDesc}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => flatFormerStepInversion isFlatFormation cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

/-- **A flat former cell admits no weak-head step.**  The flat twin of `formationGenerator_noWeakHeadStep`: a
flat formation generator (`flatTypingRuleDescOf generator = some rule`) is a type-former code, not an
eliminable/applicable head — so the only weak-head arms whose subject unifies pin the head to a redex
generator (`gen_app` or an eliminator) whose `flatTypingRuleDescOf` is the permanent `none`, contradicting
`isFlatFormation`.  No flat generator is named, so a future flat formation row is absorbed zero-touch.  The
weak-head-normality the `neutral`-arm reducibility gate consumes for the cohesion modalities. -/
theorem flatFormationGenerator_noWeakHeadStep {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (.mkGen generator payload children) reduct := by
  intro _reduct weakHeadStep
  cases weakHeadStep with
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | appCongruence _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | rootIota iotaStep =>
      cases iotaStep <;> nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeBoolElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeFst _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeSnd _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeNatElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeNatRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeListElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeOptionMatch _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeEitherMatch _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeIdJ _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeIdStrictRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | pathBeta _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | quotRecMk _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | quotElimMk _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | truncRecIntro _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | pathAppCongruence _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeQuotRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeQuotElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeTruncRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | gelBeta _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | scrutineeUngel _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)

end FX1Poly.Typed
