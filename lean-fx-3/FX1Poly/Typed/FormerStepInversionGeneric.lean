import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.Step
import FX1Poly.Core.StepTable

/-! # FX1Poly/Typed/FormerStepInversionGeneric
    — the CASCADE-FREE former step-inversion: a formation cell's step is a child congruence, with NO
      enumeration of the formation table (TG-1, the table-invariant foundation of the cascade-free metatheory)

`HasTypeDescSubjectReduction.lean`'s shipped `former_step_inv` proves the same conclusion but ENUMERATES the
formation generators: it `rcases typingRuleDescOf_isPiOrSigma` (formation generators are EXACTLY
`{gen_piTyCode, gen_sigmaTyCode}`) and handles each.  That enumeration is a cascade trap (polycell.md §3.16.19):
the moment a new formation row lands — a data type code (`listCode`/`optionCode`/…), a cubical former, a HIT
code — `typingRuleDescOf_isPiOrSigma` becomes false and every consumer that enumerated through it must gain a
case.

This file proves the SAME statement **without naming a single formation generator**, so a new formation row is
absorbed ZERO-TOUCH:

> `formerCellStepIsChildCongruence` — for any `generator` with `typingRuleDescOf generator = some rule`, a
> `Step (mkGen generator payload children) target` is necessarily a child congruence (`∃ children', target =
> mkGen generator payload children' ∧ StepChildren children children'`).

## How it dodges BOTH tables

TABLE-ROUTED (uniform-table-redex directive): the step crosses the IOTA-T1 adequacy and is inverted by the
freed-subject `StepOverTable.invertOrCong` — TWO arms, not eighteen.  The CONG disjunct IS the conclusion
(children transported back by `toStepChildren`).  The ROW-FIRING disjunct is refuted by ONE permanent
cross-table fact, `legacyElimHead_hasNoFormationRule`: every legacy row's eliminator head (`gen_app`, the
eliminators) carries NO formation rule, so the cell identification pins `typingRuleDescOf generator` to
`none`, contradicting `isFormation`.  No formation generator is ever enumerated — a new formation row is
absorbed zero-touch, and a new IOTA ROW costs exactly one `rfl` entry in the cross-table fact.

## Zero-axiom verification

`invertOrCong` + a 17-case `rfl` membership enumeration + `Option.noConfusion`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **No legacy row's eliminator head carries a formation rule** — the
permanent cross-table fact: the operational table's 17 eliminator heads
(`gen_app` and the data/identity eliminators) are disjoint from the
formation table's domain.  One `rfl` per row; a new iota row owes
exactly one new entry. -/
theorem legacyElimHead_hasNoFormationRule :
    ∀ rule : IotaRuleDesc, rule ∈ iotaRuleTable →
      typingRuleDescOf rule.elimGenerator = none := by
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
                                          | tail _ isRow => cases isRow

/-- **Cascade-free former step-inversion.**  A step out of any cell whose head carries a formation rule
(`typingRuleDescOf generator = some rule`) is a child congruence — proven without enumerating the formation
table, so every future formation row (data / cubical / HIT / IR codes) is absorbed zero-touch.  The
table-generic successor to the enumerating `former_step_inv`. -/
theorem formerCellStepIsChildCongruence {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  exact Step.childCongruenceOfElimHeadsExcluded
    legacyElimHead_hasNoFormationRule isFormation step

end FX1Poly.Typed
