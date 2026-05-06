import LeanFX2.Effects.Foundation

/-! # Effects/Step - row-level effect operation steps

This module replaces the previous empty scaffold with a small
zero-axiom semantics for effect-row operations.

It is deliberately row-level, not a term-level `effectHandle`
beta rule.  The current typed-term constructor `Term.effectPerform`
still carries an opaque raw `effectTag`, so full handler reduction
must wait until term indices expose effect rows and operation
signatures directly.

What ships here:

* operation signatures with an effect label, argument carrier, and
  result carrier;
* `CanPerform row operation`, including the built-in `Write`-allows-
  `Read` subeffect case;
* an effect action/step relation for performing an operation;
* monotonicity under row subset and row join;
* determinism of the result carrier for a fixed row/action.
-/

namespace LeanFX2.Effects

universe payloadLevel

/-- A row-level effect operation signature.

`PayloadType` is intentionally abstract: later bridges can instantiate
it with kernel `Ty`, surface syntax payloads, or a smaller test carrier
without changing the row semantics. -/
structure OperationSignature (PayloadType : Type payloadLevel) :
    Type payloadLevel where
  /-- The effect capability required by this operation. -/
  effectLabel : EffectLabel
  /-- The carrier expected by the operation argument. -/
  argumentCarrier : PayloadType
  /-- The carrier produced by the operation result. -/
  resultCarrier : PayloadType

/-- A row has permission to perform an operation.

The direct constructor checks membership of the operation's own label.
The `readViaWrite` constructor is the built-in subeffect rule: a row
that contains `Write` can also perform `Read` operations. -/
inductive CanPerform {PayloadType : Type payloadLevel}
    (availableRow : EffectRow) :
    OperationSignature PayloadType → Prop where
  /-- The row directly contains the required effect label. -/
  | direct {operation : OperationSignature PayloadType} :
      EffectRow.Member operation.effectLabel availableRow →
      CanPerform availableRow operation
  /-- `Write` subsumes `Read` for operation permission. -/
  | readViaWrite
      (argumentCarrier resultCarrier : PayloadType) :
      EffectRow.Member EffectLabel.write availableRow →
      CanPerform availableRow
        { effectLabel := EffectLabel.read
          argumentCarrier := argumentCarrier
          resultCarrier := resultCarrier }

namespace CanPerform

/-- Operation permission is monotone in the effect row preorder. -/
theorem mono
    {PayloadType : Type payloadLevel}
    {firstRow secondRow : EffectRow}
    {operation : OperationSignature PayloadType}
    (rowSubset : EffectRow.subset firstRow secondRow)
    (canPerformInFirst : CanPerform firstRow operation) :
    CanPerform secondRow operation := by
  cases canPerformInFirst with
  | direct memberProof =>
      exact CanPerform.direct (rowSubset _ memberProof)
  | readViaWrite argumentCarrier resultCarrier writeMember =>
      exact CanPerform.readViaWrite argumentCarrier resultCarrier
        (rowSubset _ writeMember)

/-- An operation allowed by the left row is allowed by the joined row. -/
theorem join_left
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {operation : OperationSignature PayloadType}
    (canPerformInFirst : CanPerform firstRow operation) :
    CanPerform (EffectRow.join firstRow secondRow) operation :=
  mono (EffectRow.join_subset_left firstRow secondRow) canPerformInFirst

/-- An operation allowed by the right row is allowed by the joined row. -/
theorem join_right
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {operation : OperationSignature PayloadType}
    (canPerformInSecond : CanPerform secondRow operation) :
    CanPerform (EffectRow.join firstRow secondRow) operation :=
  mono (EffectRow.join_subset_right firstRow secondRow) canPerformInSecond

end CanPerform

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
