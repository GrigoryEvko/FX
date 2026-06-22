import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescSubjectStronglyNormalizing
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer

/-! # FX1Poly/Typed/TermIndexedFormerStrongNormalization
    — the TERM-INDEXED-table twins of the cascade-free former step-inversion + SN driver +
      weak-head-normality (the `termIndexedFormerDescOf` analogues of `formerCellStepIsChildCongruence` /
      `formerCellStronglyNormalizingOfChildren` / `formationGenerator_noWeakHeadStep`)

The term-indexed type-formers (the identity type `gen_idCode` and the bridge/parametricity former
`gen_bridgeCode`, both arity-3 `[carrier, left, right]`) carry NO `typingRuleDescOf` row and NO
`flatTypingRuleDescOf` row — they are typed by the union's flat-family-sibling `formationRule` arm over
`termIndexedFormerDescOf` (the head child is the carrier at a universe code, the tail children are the
endpoints at the carrier).  So neither the cumulative-keyed lemmas nor the flat-keyed lemmas
(`FlatFormerStrongNormalization`) apply.  This file ships the IDENTICAL constructions keyed on the
term-indexed table, so an `Id`/`Bridge` cell is SN once its children (carrier + endpoints) are, and heads no
weak-head step.

Every twin routes through the SAME table-generic cores the cumulative / flat versions use —
`termIndexedFormerStepInversion` through `Step.childCongruenceOfElimHeadsExcluded` (GENERIC over the table
valuation), `termIndexedFormerCellStronglyNormalizing` through `formerCell_isStronglyNormalizing_of_accChildren`.
The exclusion certificate `legacyElimHead_hasNoTermIndexedFormationRule` is the one cross-table fact: every
operational row's eliminator head carries NO term-indexed formation rule (one `rfl` per row).  Third
instantiation of the cascade-free pattern (after `typingRuleDescOf` and `flatTypingRuleDescOf`).

## Zero-axiom verification

`Step.childCongruenceOfElimHeadsExcluded` + a 17-case `rfl` membership enumeration + `Option.noConfusion`
(step inversion); `formerCell_isStronglyNormalizing_of_accChildren` +
`accStepChildrenSuccessor_of_allStronglyNormalizing` (SN driver); a `cases` over the weak-head-step
constructors, each pinning the head to a redex generator whose `termIndexedFormerDescOf` is the permanent
`none` (weak-head-normality).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **No operational row's eliminator head carries a TERM-INDEXED formation rule** — the term-indexed-table
exclusion certificate: every operational row's eliminator head (`gen_app` and the data/identity eliminators)
is disjoint from the term-indexed formation table's domain (which is exactly `{gen_idCode, gen_bridgeCode}`).
One `rfl` per row; a new iota row owes exactly one new entry. -/
theorem legacyElimHead_hasNoTermIndexedFormationRule :
    ∀ rule : IotaRuleDesc, rule ∈ iotaRuleTable →
      termIndexedFormerDescOf rule.elimGenerator = none := by
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

/-- **Term-indexed-former step inversion.**  A step out of any cell whose head carries a TERM-INDEXED
formation rule (`termIndexedFormerDescOf generator = some rule`) is a child congruence — proven without
enumerating the term-indexed table (the table-generic `Step.childCongruenceOfElimHeadsExcluded` at the
term-indexed exclusion certificate), so a future term-indexed formation row is absorbed zero-touch. -/
theorem termIndexedFormerStepInversion {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TermIndexedFormerDesc} {target : RawTerm scope}
    (isTermIndexedFormation : termIndexedFormerDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' :=
  Step.childCongruenceOfElimHeadsExcluded
    legacyElimHead_hasNoTermIndexedFormationRule isTermIndexedFormation step

/-- **A term-indexed former cell with all children strongly normalizing is strongly normalizing.**
CASCADE-FREE generic assembly (the term-indexed twin of `formerCellStronglyNormalizingOfChildren`): a
term-indexed formation generator heads no root redex (`termIndexedFormerStepInversion`), so every Step out of
the cell is a child congruence; the cell is therefore SN once its child spine is accessible, which
all-children-SN supplies via `accStepChildrenSuccessor_of_allStronglyNormalizing`. -/
theorem termIndexedFormerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TermIndexedFormerDesc}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isTermIndexedFormation : termIndexedFormerDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => termIndexedFormerStepInversion isTermIndexedFormation cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

/-- **A term-indexed former cell admits no weak-head step.**  The term-indexed twin of
`formationGenerator_noWeakHeadStep`: a term-indexed formation generator
(`termIndexedFormerDescOf generator = some rule`) is a type-former code, not an eliminable/applicable head —
so the only weak-head arms whose subject unifies pin the head to a redex generator (`gen_app` or an
eliminator) whose `termIndexedFormerDescOf` is the permanent `none`, contradicting
`isTermIndexedFormation`.  The weak-head-normality the `neutral`-arm reducibility gate consumes for `Id`/
`Bridge`. -/
theorem termIndexedFormationGenerator_noWeakHeadStep {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : TermIndexedFormerDesc} (isTermIndexedFormation : termIndexedFormerDescOf generator = some rule) :
    ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (.mkGen generator payload children) reduct := by
  intro _reduct weakHeadStep
  cases weakHeadStep with
  | beta => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | appCongruence _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | rootIota iotaStep =>
      cases iotaStep <;> nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeBoolElim _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeFst _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeSnd _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeNatElim _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeNatRec _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeListElim _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeOptionMatch _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeEitherMatch _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeIdJ _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeIdStrictRec _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | pathBeta _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | quotRecMk _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | quotElimMk _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | truncRecIntro _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | pathAppCongruence _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeQuotRec _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeQuotElim _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeTruncRec _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | gelBeta _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)
  | scrutineeUngel _ => nomatch (show (none : Option TermIndexedFormerDesc) = some rule from isTermIndexedFormation)

end FX1Poly.Typed
