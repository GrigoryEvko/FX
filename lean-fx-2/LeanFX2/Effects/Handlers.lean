import LeanFX2.Effects.Step

/-! # Effects/Handlers - row-level handler cases

This module gives the previous handler scaffold a minimal, honest
row-level semantics.  A handler case packages an operation together
with the row evidence that the handler is allowed to interpret that
operation.

This is not yet a term-level algebraic-effect handler.  In particular,
there is still no `Term.effectHandle` constructor and no runtime
continuation semantics here.  The theorem below only connects a
row-level handler case to the row-level `Effects.Step` relation.
-/

namespace LeanFX2.Effects

universe payloadLevel

/-- A single handler case for one operation signature. -/
structure HandlerCase (PayloadType : Type payloadLevel) :
    Type payloadLevel where
  /-- The operation interpreted by this handler case. -/
  operation : OperationSignature PayloadType
  /-- The effect row available to the handler body. -/
  handlerRow : EffectRow
  /-- Evidence that the handler row permits this operation. -/
  canPerformOperation : CanPerform handlerRow operation

/-- A handler case handles exactly its packaged operation. -/
inductive Handles {PayloadType : Type payloadLevel}
    (handlerCase : HandlerCase PayloadType) :
    Action PayloadType → PayloadType → Prop where
  /-- Handling the packaged operation yields its result carrier. -/
  | perform :
      Handles handlerCase
        (.perform handlerCase.operation)
        handlerCase.operation.resultCarrier

namespace Handles

/-- A handled operation is a valid row-level effect step. -/
theorem to_step
    {PayloadType : Type payloadLevel}
    {handlerCase : HandlerCase PayloadType}
    {observedAction : Action PayloadType}
    {resultCarrier : PayloadType}
    (handledAction : Handles handlerCase observedAction resultCarrier) :
    Step handlerCase.handlerRow observedAction resultCarrier := by
  cases handledAction
  exact Step.perform handlerCase.canPerformOperation

/-- For a fixed handler case and action, the handled result carrier is unique. -/
theorem result_deterministic
    {PayloadType : Type payloadLevel}
    {handlerCase : HandlerCase PayloadType}
    {observedAction : Action PayloadType}
    {firstResult secondResult : PayloadType}
    (firstHandled : Handles handlerCase observedAction firstResult)
    (secondHandled : Handles handlerCase observedAction secondResult) :
    firstResult = secondResult := by
  cases firstHandled <;> cases secondHandled <;> rfl

end Handles

/-! ## Smoke example -/

/-- A concrete IO handler case induces a valid row-level step. -/
example :
    Step (EffectRow.singleton EffectLabel.io)
      (.perform
        ({ effectLabel := EffectLabel.io
           argumentCarrier := "request"
           resultCarrier := "response" } :
          OperationSignature String))
      "response" := by
  exact Handles.to_step
    (handlerCase :=
      { operation :=
          { effectLabel := EffectLabel.io
            argumentCarrier := "request"
            resultCarrier := "response" }
        handlerRow := EffectRow.singleton EffectLabel.io
        canPerformOperation :=
          CanPerform.direct (EffectRow.Member.head []) })
    Handles.perform

end LeanFX2.Effects
