import LeanFX2.Codata.Foundation

/-! # Codata/Step - stream observation steps

This module replaces the previous empty scaffold with a small
zero-axiom step semantics for the codata fragment that actually ships:
`Stream alpha`.

It does not claim a generic user-defined codata eliminator.  The
generic `Ty.codata` kernel beta rule lives in `Reduction.Step`; this
module records the rich-layer stream destructor view that corresponds
to `head` and `tail`.
-/

namespace LeanFX2.Codata
namespace Stream

variable {alpha : Type}

/-- The destructors available for the shipped `Stream` codata fragment. -/
inductive Destructor (alpha : Type) : Type where
  /-- Observe the current stream head. -/
  | head : Destructor alpha
  /-- Observe the remaining stream tail. -/
  | tail : Destructor alpha

namespace Destructor

/-- Result carrier of a stream destructor. -/
def Result : Destructor alpha → Type
  | .head => alpha
  | .tail => Stream alpha

end Destructor

/-- One codata observation step for streams. -/
inductive Step (someStream : Stream alpha) :
    (destructor : Destructor alpha) → destructor.Result → Prop where
  /-- Observing `head` yields `Stream.head someStream`. -/
  | head : Step someStream .head (Stream.head someStream)
  /-- Observing `tail` yields `Stream.tail someStream`. -/
  | tail : Step someStream .tail (Stream.tail someStream)

namespace Step

/-- Head observation is deterministic for a fixed stream. -/
theorem head_deterministic
    {someStream : Stream alpha}
    {firstValue secondValue : alpha}
    (firstStep : Step someStream .head firstValue)
    (secondStep : Step someStream .head secondValue) :
    firstValue = secondValue := by
  cases firstStep
  cases secondStep
  rfl

/-- Tail observation is deterministic for a fixed stream. -/
theorem tail_deterministic
    {someStream : Stream alpha}
    {firstTail secondTail : Stream alpha}
    (firstStep : Step someStream .tail firstTail)
    (secondStep : Step someStream .tail secondTail) :
    firstTail = secondTail := by
  cases firstStep
  cases secondStep
  rfl

/-- Bisimilar streams have equal head observations. -/
theorem head_respects_bisim
    {firstStream secondStream : Stream alpha}
    {firstValue secondValue : alpha}
    (streamsBisim : Bisim firstStream secondStream)
    (firstStep : Step firstStream .head firstValue)
    (secondStep : Step secondStream .head secondValue) :
    firstValue = secondValue := by
  cases firstStep
  cases secondStep
  exact bisim_head streamsBisim

/-- Bisimilar streams have bisimilar tail observations. -/
theorem tail_respects_bisim
    {firstStream secondStream : Stream alpha}
    {firstTail secondTail : Stream alpha}
    (streamsBisim : Bisim firstStream secondStream)
    (firstStep : Step firstStream .tail firstTail)
    (secondStep : Step secondStream .tail secondTail) :
    Bisim firstTail secondTail := by
  cases firstStep
  cases secondStep
  exact bisim_tail streamsBisim

/-- The head observation of an unfolded stream computes to the first
step result. -/
theorem head_unfold
    {state : Type}
    (stepFunction : state → alpha × state)
    (initialState : state) :
    Step (unfold stepFunction initialState)
      .head
      (stepFunction initialState).1 :=
  Step.head

/-- The tail observation of an unfolded stream is bisimilar to unfolding
from the advanced state. -/
theorem tail_unfold_bisim
    {state : Type}
    (stepFunction : state → alpha × state)
    (initialState : state)
    {observedTail : Stream alpha}
    (tailStep :
      Step (unfold stepFunction initialState) .tail observedTail) :
    Bisim observedTail (unfold stepFunction (stepFunction initialState).2) := by
  cases tailStep
  exact Stream.tail_unfold stepFunction initialState

end Step

/-! ## Smoke examples -/

/-- The head step of the natural-number stream observes its head value. -/
example :
    Step naturals (Destructor.head : Destructor Nat) (Stream.head naturals) :=
  Step.head

/-- The tail step of `constantZero` observes a stream bisimilar to itself. -/
example
    {observedTail : Stream Nat}
    (tailStep : Step constantZero (Destructor.tail : Destructor Nat) observedTail) :
    Bisim observedTail constantZero := by
  cases tailStep
  intro _observedIndex
  rfl

end Stream
end LeanFX2.Codata
