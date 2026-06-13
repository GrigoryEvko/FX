import FX1Poly.Typed.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.HasTypeDescPiContextStepConversion
import FX1Poly.Core.StepTable

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormerSubjectReduction — NATIVE-15: context-conversion + subject reduction

`HasTypeDescTermIndexedFormer` (NATIVE-12) types `Id A a b` / `Bridge A a b` through ONE generic arm; NATIVE-13/14
gave its renaming/substitution/inversion/uniqueness.  This file lands the last two structural-metatheory pieces —
the parity with the formation/flat/grown engines:

  * **context-conversion** (EXACT) — a term-indexed-former derivation re-types under a context whose entries are
    `Conv`-related to the originals AND remain valid in the new context (`ConvContextWithOldValid`), preserving the
    classifier EXACTLY.  Each grown premise (carrier + endpoints) lifts through the shipped unconditional grown
    `HasTypeDescPi.contextConversionExact`; no binder crosses (the Id/Bridge children all live in the base context,
    all shifts `0`), so no `ConvContextWithOldValid.cons` is needed.
  * **subject reduction** — a term-indexed-former derivation is preserved under any `Step` of its subject, at the
    SAME classifier (the SR-dispatcher arm for the engine).  The Id/Bridge cell heads NO root redex (the 18 Step
    arms all force `termIndexedFormerDescOf = none`), so a `Step` is a child congruence; the premise telescope is
    re-typed under the stepped children.

## The carrier-steps subtlety (why this is richer than the flat SR)

The flat telescope's siblings are all typed at a universe (no inter-child dependency), so flat SR just re-types
each stepped child.  Here the endpoints are typed AT THE CARRIER (the first child).  When the CARRIER child steps
`A ↝ A'`, the new telescope's carrier index is `A'`, so the endpoints — formerly `eᵢ : A` — must be re-classified
to `eᵢ : A'`.  That is exactly the grown `conv` arm: `Conv A A'` (from the step) plus the SR'd carrier typing
`A' : Type@level` (the new reclassifier) re-class each endpoint.  When an ENDPOINT steps the carrier is fixed and
only that endpoint is re-typed by the grown SR.  The former's output classifier (`universeCodeCell level flag`,
the carrier's universe) is untouched by any child step — level/flag survive the carrier's SR — so the headline
preserves the classifier exactly.

## Zero-axiom

The grown SR/context-conversion/`conv` are themselves zero-axiom; `termIndexedFormerCellStepIsChildCongruence` is
the 18-arm `cases step` clone keyed on `termIndexedFormerDescOf` (`nomatch` on the 16 ι+ β redex heads, the `cong`
arm extracts the child step); the telescope helpers are structural `match`-recursion + nested `cases stepChildren`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Context-conversion (EXACT, via `ConvContextWithOldValid`) -/

/-- **Endpoint context-conversion (EXACT).**  Re-types each endpoint through the shipped unconditional grown
`HasTypeDescPi.contextConversionExact`, at the SAME carrier classifier.  Structural `match`-recursion. -/
theorem TermIndexedEndpoints.contextConversionExact {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {carrier : RawTerm scope}
    {shifts : List Nat} {rest : RawTermChildren shifts scope}
    (endpoints : TermIndexedEndpoints profile sourceContext carrier rest) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      TermIndexedEndpoints profile targetContext carrier rest :=
  match endpoints with
  | .nil => fun _targetContext _enriched => .nil
  | .cons endpoint rest endpointTyped restTyped =>
      fun targetContext enriched =>
        .cons endpoint rest
          (HasTypeDescPi.contextConversionExact endpointTyped targetContext enriched)
          (TermIndexedEndpoints.contextConversionExact restTyped targetContext enriched)

/-- **Telescope context-conversion (EXACT).**  The carrier head re-types at its universe code through the grown
`contextConversionExact` (EXACT, same classifier); the endpoints lift via the endpoint companion.  No binder
crosses (all term-indexed children share the base context), so no `ConvContextWithOldValid.cons`. -/
theorem TermIndexedFormerTelescope.contextConversionExact {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (telescope : TermIndexedFormerTelescope profile sourceContext children carrier level flag) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      TermIndexedFormerTelescope profile targetContext children carrier level flag :=
  match telescope with
  | .mk carrier rest level flag carrierTyped endpointsTyped =>
      fun targetContext enriched =>
        .mk carrier rest level flag
          (HasTypeDescPi.contextConversionExact carrierTyped targetContext enriched)
          (TermIndexedEndpoints.contextConversionExact endpointsTyped targetContext enriched)

/-- **★ Term-indexed former context-conversion (EXACT).**  A `HasTypeDescTermIndexedFormer` derivation re-types
under an enriched context conversion, preserving the classifier exactly — the term-indexed twin of the grown
`HasTypeDescPi.contextConversionExact`.  Single-arm `cases`; the premise telescope lifts via its companion. -/
theorem HasTypeDescTermIndexedFormer.contextConversionExact {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescTermIndexedFormer profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      HasTypeDescTermIndexedFormer profile targetContext subject classifier := by
  cases derivation with
  | genFormation generator payload children carrier level flag rule isTermIndexed premises =>
      intro targetContext enriched
      exact HasTypeDescTermIndexedFormer.genFormation targetContext generator payload children
        carrier level flag rule isTermIndexed
        (TermIndexedFormerTelescope.contextConversionExact premises targetContext enriched)

/-! ## Subject reduction -/

/-- **No legacy row's eliminator head carries a term-indexed-former rule** —
the term-indexed-table exclusion certificate: one `rfl` per row. -/
theorem legacyElimHead_hasNoTermIndexedFormerRule :
    ∀ rule : FX1Poly.Core.IotaRuleDesc, rule ∈ FX1Poly.Core.iotaRuleTable →
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
                                          | tail _ isRow => cases isRow

/-- **Term-indexed former step inversion.**  An `Id`/`Bridge` former cell heads no root redex, so any `Step` out
of it is a child congruence — TABLE-ROUTED: the generic `Step.childCongruenceOfElimHeadsExcluded` at the
term-indexed-table exclusion certificate (two arms, not eighteen). -/
theorem termIndexedFormerCellStepIsChildCongruence {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TermIndexedFormerDesc} {target : RawTerm scope}
    (isTermIndexed : termIndexedFormerDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' :=
  Step.childCongruenceOfElimHeadsExcluded
    legacyElimHead_hasNoTermIndexedFormerRule isTermIndexed step

/-- **Endpoint carrier-reclassification along `Conv`.**  When the carrier steps `A ↝ A'`, each endpoint `eᵢ : A`
must be re-classified to `eᵢ : A'`.  The grown `conv` arm does it: `Conv A A'` plus the new carrier typing
`A' : Type@level` re-class each endpoint.  Structural `match`-recursion. -/
theorem TermIndexedEndpoints.convCarrier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier carrierAfter : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {shifts : List Nat} {rest : RawTermChildren shifts scope}
    (endpoints : TermIndexedEndpoints profile context carrier rest)
    (carrierConv : Conv carrier carrierAfter)
    (carrierAfterTyped : HasTypeDescPi profile context carrierAfter (universeCodeCell level flag)) :
    TermIndexedEndpoints profile context carrierAfter rest :=
  match endpoints with
  | .nil => .nil
  | .cons endpoint rest endpointTyped restTyped =>
      .cons endpoint rest
        (HasTypeDescPi.conv level flag endpointTyped carrierConv carrierAfterTyped)
        (TermIndexedEndpoints.convCarrier restTyped carrierConv carrierAfterTyped)

/-- **Endpoint subject reduction (carrier fixed).**  Re-types the endpoints under a `StepChildren` of the
endpoint spine, with the carrier classifier unchanged: the stepped endpoint re-types via the grown SR, the others
stay.  Structural `match`-recursion + nested `cases stepChildren`.  Threads `WfContextDescPi` for the grown SR. -/
theorem TermIndexedEndpoints.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier : RawTerm scope}
    {shifts : List Nat} {rest : RawTermChildren shifts scope}
    (endpoints : TermIndexedEndpoints profile context carrier rest)
    (wellFormed : WfContextDescPi context) :
    ∀ (rest' : RawTermChildren shifts scope),
      StepChildren rest rest' → TermIndexedEndpoints profile context carrier rest' :=
  match endpoints with
  | .nil => fun _rest' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons endpoint rest endpointTyped restTyped =>
      fun _rest' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i endpointAfter
            exact TermIndexedEndpoints.cons endpointAfter rest
              (HasTypeDescPi.subjectReduction endpointTyped wellFormed endpointAfter headStep)
              restTyped
        | there _head restStep =>
            rename_i restAfter
            exact TermIndexedEndpoints.cons endpoint restAfter endpointTyped
              (TermIndexedEndpoints.subjectReduction restTyped wellFormed restAfter restStep)

/-- **Telescope subject reduction.**  Re-types the full term-indexed premise under a `StepChildren` of the cell's
children.  The `here` (carrier-head step) case SR's the carrier, then re-classifies the endpoints from the old to
the new carrier via `convCarrier` (`Conv` from the step).  The `there` (endpoint step) case keeps the carrier and
re-types the endpoints via `TermIndexedEndpoints.subjectReduction`.  Existential in the new carrier; the level/flag
are preserved (the carrier's SR keeps its universe).  Stated over a FREE shift index so `cases telescope` unifies. -/
theorem TermIndexedFormerTelescope.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (telescope : TermIndexedFormerTelescope profile context children carrier level flag)
    (wellFormed : WfContextDescPi context)
    {children' : RawTermChildren shifts scope}
    (stepChildren : StepChildren children children') :
    ∃ carrier', TermIndexedFormerTelescope profile context children' carrier' level flag := by
  cases telescope with
  | mk _carrier restEndpoints _level _flag carrierTyped endpointsTyped =>
      cases stepChildren with
      | here _rest headStep =>
          rename_i carrierAfter
          have carrierAfterTyped :=
            HasTypeDescPi.subjectReduction carrierTyped wellFormed carrierAfter headStep
          exact ⟨carrierAfter, TermIndexedFormerTelescope.mk carrierAfter restEndpoints
            level flag carrierAfterTyped
            (TermIndexedEndpoints.convCarrier endpointsTyped (Conv.fromStep headStep) carrierAfterTyped)⟩
      | there _head restStep =>
          rename_i restAfter
          exact ⟨carrier, TermIndexedFormerTelescope.mk carrier restAfter
            level flag carrierTyped
            (TermIndexedEndpoints.subjectReduction endpointsTyped wellFormed restAfter restStep)⟩

/-- **★ Term-indexed former subject reduction.**  A `HasTypeDescTermIndexedFormer` derivation is preserved under a
`Step` of its subject, at the SAME classifier — the SR-dispatcher arm for the engine, the term-indexed twin of
the union's `flatFormation`-arm subject reduction.  The `Id`/`Bridge` cell heads no root redex
(`termIndexedFormerCellStepIsChildCongruence`), so the step is a child congruence; the premise re-types via
`TermIndexedFormerTelescope.subjectReduction` (new carrier, same level/flag), and the classifier
(`rule.outputType scope level flag = universeCodeCell level flag`, the carrier's universe) is unchanged. -/
theorem HasTypeDescTermIndexedFormer.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescTermIndexedFormer profile context subject classifier)
    (wellFormed : WfContextDescPi context) :
    ∀ (reduct : RawTerm scope), Step subject reduct →
      HasTypeDescTermIndexedFormer profile context reduct classifier := by
  cases derivation with
  | genFormation generator payload children carrier level flag rule isTermIndexed premises =>
      intro _reduct step
      obtain ⟨children', reductEq, stepChildren⟩ :=
        termIndexedFormerCellStepIsChildCongruence isTermIndexed step
      subst reductEq
      obtain ⟨carrier', premises'⟩ :=
        TermIndexedFormerTelescope.subjectReduction premises wellFormed stepChildren
      exact HasTypeDescTermIndexedFormer.genFormation context generator payload children'
        carrier' level flag rule isTermIndexed premises'

end FX1Poly.Typed
