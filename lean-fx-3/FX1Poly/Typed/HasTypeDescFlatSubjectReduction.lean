import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescSubjectReduction

/-! # FX1Poly/Typed/HasTypeDescFlatSubjectReduction
    — subject reduction for the flat-former typing judgment (next #935 increment)

`HasTypeDescFlat` (the standalone flat-former engine, #934) types the non-dependent `[0,0]` type-code formers
`product` / `sum` / `either` / `arrow` / `equiv`.  Its metatheory needs the same subject-reduction the cumulative
engine has (`HasTypeDesc.subjectReduction`): a flat-former derivation is preserved under any `Step` of its
subject, at the SAME classifier.  This file supplies it — the flat twin of `HasTypeDesc.subjectReduction`.

## The three-step shape (mirrors the cumulative engine, simpler at the telescope)

1. `flatFormerCellStepIsChildCongruence` — the flat-former cell heads NO root redex.  A clone of
   `formerCellStepIsChildCongruence` keyed on the FLAT table: each of the 18 redex `Step` arms (cong + beta + 16
   iotas) is ruled out because `flatTypingRuleDescOf generator = some rule` while the redex head would force
   `flatTypingRuleDescOf generator = none` — exactly the same `nomatch (show (none : Option …) = some rule …)`
   contradiction the cumulative inversion uses.  So any `Step` of a flat-former cell is a child congruence.

2. `FlatDescTelescope.subjectReduction` — re-types the premise telescope under the stepped children.  SIMPLER
   than `DescTelescope.subjectReduction`: the flat `cons` does NOT extend the context (all siblings share the
   base context, shifts all-`0`), so the `here` arm re-types the stepped head via `HasTypeDesc.subjectReduction`
   and keeps the tail under the SAME context — no `convTelescope`, no `convContextCondition_consStep`.  `there`
   recurses into the tail.  Term-mode `match`-recursion (the `FlatDescTelescope` is standalone, so structural
   recursion over it is available directly).

3. `HasTypeDescFlat.subjectReduction` — the headline.  Cases the (single-constructor) derivation, inverts the
   `Step` to a child congruence (1), re-types the premise (2), and rebuilds the `flatFormation` derivation at the
   unchanged classifier (`rule.outputType` of the unchanged levels — the levels are not touched by a child step).

## Zero-axiom verification

`flatFormerCellStepIsChildCongruence` is an 18-arm `cases step` (one congruence arm + 17 `nomatch`
contradictions).  `FlatDescTelescope.subjectReduction` is structural `match`-recursion with a nested `cases
stepChildren` (`here` / `there`).  `HasTypeDescFlat.subjectReduction` is a single-arm `cases derivation` —
binding the constructor's 8 fields (the `context` is the inductive's auto-determined INDEX, NOT a bound field) —
plus `obtain` + `subst` + a constructor re-application.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Flat-former step inversion.**  A flat-former cell heads no root redex, so any `Step` out of it is a child
congruence.  Clone of `formerCellStepIsChildCongruence` keyed on the FLAT table (`flatTypingRuleDescOf`): each
redex head has `flatTypingRuleDescOf = none` by rfl, so the `some rule` hypothesis contradicts every redex arm,
exactly as for the cumulative table.  Leaves only the `cong` arm, which exposes the child step directly. -/
theorem flatFormerCellStepIsChildCongruence {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  cases step with
  | cong _ _ childStep => exact ⟨_, rfl, childStep⟩
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaBoolTrue => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaBoolFalse => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaFstPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaSndPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatElimZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatRecZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaListElimNil => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaOptionMatchNone => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaOptionMatchSome => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaEitherMatchInl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaEitherMatchInr => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatElimSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatRecSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaListElimCons => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaIdJRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaIdStrictRecRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)

/-- **Flat telescope subject reduction.**  Re-types a `FlatDescTelescope` premise under stepped children.
Simpler than `DescTelescope.subjectReduction`: the flat `cons` does NOT extend the context (all siblings share
the base context), so the `here` arm re-types the stepped head via `HasTypeDesc.subjectReduction` and keeps the
tail under the SAME context (no `convTelescope`).  `there` recurses into the tail.  Structural `match`-recursion
over the standalone telescope. -/
theorem FlatDescTelescope.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∀ (children' : RawTermChildren binderShifts scope),
      StepChildren children children' → FlatDescTelescope profile context flag levels children' :=
  match telescope with
  | .nil => fun _children' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            exact FlatDescTelescope.cons headAfter headLevel restLevels rest
              (HasTypeDesc.subjectReduction headTyped headAfter headStep) restTyped
        | there _head restStep =>
            rename_i restAfter
            exact FlatDescTelescope.cons head headLevel restLevels restAfter headTyped
              (FlatDescTelescope.subjectReduction restTyped restAfter restStep)

/-- **★ Flat-former subject reduction.**  A `HasTypeDescFlat` derivation is preserved under a `Step` of its
subject, at the SAME classifier — the flat-engine twin of `HasTypeDesc.subjectReduction`.  The flat-former cell
heads no root redex (`flatFormerCellStepIsChildCongruence`), so the `Step` is a child congruence; the premise
telescope is re-typed via `FlatDescTelescope.subjectReduction`, and the classifier (`rule.outputType` of the
unchanged levels) is preserved exactly — a child step touches neither the generator nor the levels.

The `cases derivation with | flatFormation generator payload children levels flag rule isFlat premise` binds the
constructor's 8 explicit fields; the `context` is the inductive's auto-determined INDEX (the theorem's own
`context`) and must NOT be bound. -/
theorem HasTypeDescFlat.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context subject classifier) :
    ∀ (reduct : RawTerm scope), Step subject reduct →
      HasTypeDescFlat profile context reduct classifier := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      intro _reduct step
      obtain ⟨children', reductEq, stepChildren⟩ := flatFormerCellStepIsChildCongruence isFlat step
      subst reductEq
      exact HasTypeDescFlat.flatFormation context generator payload children' levels flag rule isFlat
        (FlatDescTelescope.subjectReduction premise children' stepChildren)

end FX1Poly.Typed
