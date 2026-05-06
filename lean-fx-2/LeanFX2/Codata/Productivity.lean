import LeanFX2.Codata.Foundation

/-! # Codata/Productivity - stream productivity predicate

This module states productivity for the codata fragment that actually
ships: streams encoded as total functions `Nat -> alpha`.

It is not a guardedness checker for user-written corecursive syntax.
That later checker needs a surface elaborator and either sized types or
a `Later`-modality discipline.  Here we expose the invariant already
guaranteed by the function encoding and prove it is preserved by the
available stream destructors and bisimulation.
-/

namespace LeanFX2.Codata
namespace Stream

variable {alpha : Type}

/-- A stream is productive when every finite observation has a value. -/
def Productive (someStream : Stream alpha) : Prop :=
  ∀ (observationIndex : Nat),
    ∃ (observedValue : alpha),
      someStream observationIndex = observedValue

/-- Every function-encoded stream is productive. -/
theorem productive_of_stream (someStream : Stream alpha) :
    Productive someStream :=
  Stream.productive someStream

/-- Productivity gives an observable head value. -/
theorem productive_head
    {someStream : Stream alpha}
    (streamProductive : Productive someStream) :
    ∃ (observedValue : alpha), head someStream = observedValue :=
  streamProductive 0

/-- Productivity is preserved by tail observation. -/
theorem productive_tail
    {someStream : Stream alpha}
    (streamProductive : Productive someStream) :
    Productive (tail someStream) :=
  fun observationIndex => streamProductive (observationIndex + 1)

/-- Unfolded streams are productive. -/
theorem productive_unfold
    {state : Type}
    (stepFunction : state → alpha × state)
    (initialState : state) :
    Productive (unfold stepFunction initialState) :=
  productive_of_stream _

/-- Bisimulation preserves productivity. -/
theorem productive_of_bisim
    {firstStream secondStream : Stream alpha}
    (streamsBisim : Bisim firstStream secondStream)
    (firstProductive : Productive firstStream) :
    Productive secondStream := by
  intro observationIndex
  cases firstProductive observationIndex with
  | intro observedValue firstObserved =>
      exact ⟨observedValue, (streamsBisim observationIndex).symm.trans firstObserved⟩

/-! ## Smoke examples -/

/-- The natural-number stream is productive. -/
example : Productive naturals :=
  productive_of_stream naturals

/-- The tail of the natural-number stream is productive. -/
example : Productive (tail naturals) :=
  productive_tail (productive_of_stream naturals)

end Stream
end LeanFX2.Codata
