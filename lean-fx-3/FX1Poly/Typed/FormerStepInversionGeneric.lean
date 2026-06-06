import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.Step

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

## How it dodges the table

`cases step` over the 18 `Step` constructors.  The `cong` case IS the conclusion.  Each of the 17 ROOT-redex
constructors (`beta` + the 16 `iota*`) has a redex whose OUTERMOST head is a FIXED generator — `gen_app` for
`beta`, `gen_boolElim` for `iotaBoolTrue/False`, `gen_fst`/`gen_snd` for the projections, `gen_natElim`/… for
the recursors, etc.  Dependent elimination therefore unifies `generator` to that redex head; the hypothesis
`isFormation : typingRuleDescOf generator = some rule` becomes `typingRuleDescOf <redexHead> = some rule`, and
`typingRuleDescOf <redexHead>` reduces to `none` (a PERMANENT table fact — eliminators and `gen_app` never carry
a formation rule).  The case is closed by `nomatch (… : none = some rule)`.  No formation generator is ever
enumerated; the only table facts used are the `none`-valuations of the redex heads, which no future formation
row disturbs.  This is the `subjectRootGeneratorGeneric` discipline (the `∃ rule, typingRuleDescOf = some rule`
disjunct) applied to step inversion — the cascade-free successor `former_step_inv` should eventually delegate to.

## Zero-axiom verification

`cases step` with `generator` FREE stays propext-clean (the impossible redex cases are discharged by the
explicit `nomatch`, not by leaked impossible-case equation lemmas — the raw-routing-inversion concern does not
arise here).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

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
  cases step with
  | cong _ _ childStep => exact ⟨_, rfl, childStep⟩
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaBoolTrue => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaBoolFalse => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaFstPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaSndPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatElimZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatRecZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaListElimNil => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaOptionMatchNone => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaOptionMatchSome => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaEitherMatchInl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaEitherMatchInr => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatElimSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatRecSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaListElimCons => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaIdJRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaIdStrictRecRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

end FX1Poly.Typed
