import LeanFX2.Effects.Foundation

/-! # Effects/Step - row-level effect operation steps

This module replaces the previous empty scaffold with a small
zero-axiom semantics for effect-row operations.

It is deliberately row-level, not a term-level `effectHandle`
beta rule.  The typed-term constructor `Term.effectPerform` now
requires `CanPerform` evidence, but `Ty.effect` still carries an
opaque raw `effectTag`; full handler reduction must wait until the
type schema stores structured rows directly.

What ships here:

* operation signatures and `CanPerform` evidence from
  `Foundation.Effect`;
* an effect action/step relation for performing an operation;
* monotonicity under row subset and row join;
* determinism of the result carrier for a fixed row/action.
-/

namespace LeanFX2.Effects

universe payloadLevel

/-- A row-level effect action. -/
inductive Action (PayloadType : Type payloadLevel) : Type payloadLevel where
  /-- Perform one operation. -/
  | perform (operation : OperationSignature PayloadType) :
      Action PayloadType

/-- One row-level effect step.

`Step row action resultCarrier` states that `action` can run under
`row` and produces values of `resultCarrier`. -/
inductive Step {PayloadType : Type payloadLevel}
    (availableRow : EffectRow) :
    Action PayloadType → PayloadType → Prop where
  /-- Performing an allowed operation yields that operation's result
  carrier. -/
  | perform {operation : OperationSignature PayloadType} :
      CanPerform availableRow operation →
      Step availableRow (.perform operation) operation.resultCarrier

namespace Step

/-- Effect steps are monotone in the effect row preorder. -/
theorem mono
    {PayloadType : Type payloadLevel}
    {firstRow secondRow : EffectRow}
    {observedAction : Action PayloadType}
    {resultCarrier : PayloadType}
    (rowSubset : EffectRow.subset firstRow secondRow)
    (stepInFirst : Step firstRow observedAction resultCarrier) :
    Step secondRow observedAction resultCarrier := by
  cases stepInFirst with
  | perform canPerformInFirst =>
      exact Step.perform (CanPerform.mono rowSubset canPerformInFirst)

/-- A step allowed by the left row is allowed by the joined row. -/
theorem join_left
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {observedAction : Action PayloadType}
    {resultCarrier : PayloadType}
    (stepInFirst : Step firstRow observedAction resultCarrier) :
    Step (EffectRow.join firstRow secondRow) observedAction resultCarrier :=
  mono (EffectRow.join_subset_left firstRow secondRow) stepInFirst

/-- A step allowed by the right row is allowed by the joined row. -/
theorem join_right
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {observedAction : Action PayloadType}
    {resultCarrier : PayloadType}
    (stepInSecond : Step secondRow observedAction resultCarrier) :
    Step (EffectRow.join firstRow secondRow) observedAction resultCarrier :=
  mono (EffectRow.join_subset_right firstRow secondRow) stepInSecond

/-- For a fixed row and action, the effect result carrier is unique. -/
theorem result_deterministic
    {PayloadType : Type payloadLevel}
    {availableRow : EffectRow}
    {observedAction : Action PayloadType}
    {firstResult secondResult : PayloadType}
    (firstStep : Step availableRow observedAction firstResult)
    (secondStep : Step availableRow observedAction secondResult) :
    firstResult = secondResult := by
  cases firstStep <;> cases secondStep <;> rfl

end Step

/-! ## Smoke examples -/

/-- IO operations are allowed by a row containing IO. -/
example :
    CanPerform (EffectRow.singleton EffectLabel.io)
      ({ effectLabel := EffectLabel.io
         argumentCarrier := "request"
         resultCarrier := "response" } :
        OperationSignature String) :=
  CanPerform.direct (EffectRow.Member.head [])

/-- A row containing Write can perform a Read operation. -/
example :
    CanPerform (EffectRow.singleton EffectLabel.write)
      ({ effectLabel := EffectLabel.read
         argumentCarrier := "cell"
         resultCarrier := "value" } :
        OperationSignature String) :=
  CanPerform.readViaWrite "cell" "value" (EffectRow.Member.head [])

end LeanFX2.Effects
