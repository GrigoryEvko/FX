/-! # Codata/Foundation — coinductive types via Nat-indexed observation

Per `fx_design.md` §3.5, FX codata are coinductive types defined
by their destructors (e.g., `head`, `tail` for streams).  Lean 4's
strict-positivity rejects the obvious encoding
`structure Stream alpha { head : alpha; tail : Stream alpha }`,
so we use the *function encoding* `Stream alpha := Nat → alpha`,
which makes productivity automatic — every observation yields a
defined value because Lean enforces totality of the underlying
`Nat → alpha` function.

## What ships (Phase 12.A.6 — Codata layer foundation)

* `Stream alpha` — canonical codata example as `Nat → alpha`
* `head` / `tail` destructors with `rfl`-level reductions
* `unfold` operation: state → (alpha × state) → Stream alpha
* `Bisim` — observational equivalence (head equal + tail bisim)
* Equivalence-relation laws: refl, symm, trans
* Computation laws: `head_unfold`, `tail_unfold` (latter as Bisim)
* Productivity meta-theorem (every observation is a value)

## What defers (later phases)

* User-defined codata syntax (`codata stream<a> ... end codata`)
  — surface elaboration in Phase 14+
* Generic codata via destructor records — needs Layer-K kernel
  primitive `Ty.codata` (deferred K08)
* Productivity check for user-supplied corecursive definitions —
  needs sized-type or guardedness analysis at the kernel
* Connection to `Modal/Later` for guarded recursion (the more
  expressive alternative for codata that supports HoTT-style
  obstruction proofs)

## Why bisimulation, not equality

In a univalent or zero-axiom setting, two streams that agree at
every index are NOT propositionally equal — that conclusion would
require `funext` (function extensionality), which is a propext-
class axiom barred under our strict zero-axiom doctrine.  So we
ship `Bisim` as the canonical observational equality and prove
its equivalence-relation laws constructively.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Codata

/-! ## Stream as the canonical codata

`Stream alpha` represents an infinite sequence of `alpha` values.
Encoded as a total function `Nat → alpha`: index `n` looks up
the n-th element.  Productivity is automatic — Lean's totality
requirement guarantees every `s n` reduces to a defined value. -/

/-- Infinite stream of `alpha` values, encoded as a Nat-indexed
function.  The function encoding sidesteps Lean 4's strict-
positivity rejection of `structure Stream alpha { head, tail }`
while preserving the destructor-based interface via the
`head` / `tail` operations below. -/
@[reducible]
def Stream (alpha : Type) : Type :=
  Nat → alpha

namespace Stream

variable {alpha state : Type}

/-! ## Destructors -/

/-- The first element of a stream.  Equivalent to `someStream 0`. -/
def head (someStream : Stream alpha) : alpha :=
  someStream 0

/-- All but the first element.  Equivalent to `fun n =>
someStream (n + 1)`. -/
def tail (someStream : Stream alpha) : Stream alpha :=
  fun nextIndex => someStream (nextIndex + 1)

/-! ## Iteration utility (state advancement) -/

/-- Apply a state-transition `count` times.  This is the workhorse
for `unfold`. -/
def iterateState (advance : state → state) :
    Nat → state → state
  | 0, currentState => currentState
  | innerCount + 1, currentState =>
      iterateState advance innerCount (advance currentState)

/-! ## Unfold (the codata constructor)

`unfold step initial` produces a stream whose n-th element is
the first projection of `step` applied to the state advanced
n times. -/

/-- Build a stream from a state and a step function.  `step st =
(value, newState)` — value goes into the stream, newState is
threaded into the next observation. -/
def unfold
    (step : state → alpha × state)
    (initial : state) : Stream alpha :=
  fun observationIndex =>
    (step (iterateState (fun currentState => (step currentState).2)
                        observationIndex initial)).1

/-! ## Bisimulation (observational equivalence)

Two streams are bisimilar when they agree on every observation.
This is the canonical observational equality for codata; it
implies pointwise `Eq` but the converse is funext, which we
do not assume. -/

/-- Two streams are bisimilar when they agree at every index. -/
def Bisim (firstStream secondStream : Stream alpha) : Prop :=
  ∀ (someIndex : Nat), firstStream someIndex = secondStream someIndex

/-! ### Equivalence-relation laws -/

/-- Bisim is reflexive. -/
theorem bisim_refl (someStream : Stream alpha) : Bisim someStream someStream :=
  fun _ => rfl

/-- Bisim is symmetric. -/
theorem bisim_symm
    {firstStream secondStream : Stream alpha}
    (firstBisim : Bisim firstStream secondStream) :
    Bisim secondStream firstStream :=
  fun someIndex => (firstBisim someIndex).symm

/-- Bisim is transitive. -/
theorem bisim_trans
    {firstStream secondStream thirdStream : Stream alpha}
    (firstBisim : Bisim firstStream secondStream)
    (secondBisim : Bisim secondStream thirdStream) :
    Bisim firstStream thirdStream :=
  fun someIndex =>
    (firstBisim someIndex).trans (secondBisim someIndex)

/-! ## Computation laws -/

/-- `head` of an unfolded stream is the first projection of
`step` applied to the initial state.  Definitionally `rfl`. -/
theorem head_unfold
    (step : state → alpha × state)
    (initial : state) :
    head (unfold step initial) = (step initial).1 :=
  rfl

/-- `tail` of an unfolded stream is the unfold from the new
state.  Stated as a bisimulation (proving propositional
equality of streams would require funext). -/
theorem tail_unfold
    (step : state → alpha × state)
    (initial : state) :
    Bisim (tail (unfold step initial))
          (unfold step (step initial).2) := by
  intro someIndex
  rfl

/-! ## Bisim respects destructors -/

/-- Bisim implies head equality. -/
theorem bisim_head
    {firstStream secondStream : Stream alpha}
    (streamsBisim : Bisim firstStream secondStream) :
    head firstStream = head secondStream :=
  streamsBisim 0

/-- Bisim implies tail bisim. -/
theorem bisim_tail
    {firstStream secondStream : Stream alpha}
    (streamsBisim : Bisim firstStream secondStream) :
    Bisim (tail firstStream) (tail secondStream) :=
  fun someIndex => streamsBisim (someIndex + 1)

/-! ## Productivity (every observation is a value)

Productivity is the dual of termination — for codata, it states
that every observation reduces to a defined value.  In our
function encoding, this is automatic because `Stream alpha :=
Nat → alpha` is a total function: Lean's elaborator only
accepts total definitions. -/

/-- Productivity meta-theorem: every observation of a stream
yields a defined value.  Trivial in the function encoding —
holds by `rfl` because the stream's underlying function is total. -/
theorem productive (someStream : Stream alpha) (someIndex : Nat) :
    ∃ (observedValue : alpha), someStream someIndex = observedValue :=
  ⟨someStream someIndex, rfl⟩

end Stream

/-! ## Smoke samples -/

/-- The constant-zero stream. -/
def constantZero : Stream Nat :=
  fun _ => 0

/-- The natural numbers as a stream: 0, 1, 2, 3, ... -/
def naturals : Stream Nat :=
  Stream.unfold (fun currentNat => (currentNat, currentNat + 1)) 0

/-- The first element of `naturals` is 0. -/
example : Stream.head naturals = 0 := rfl

/-- The first element of `tail naturals` is 1. -/
example : Stream.head (Stream.tail naturals) = 1 := rfl

/-- `constantZero` is bisimilar to itself. -/
example : Stream.Bisim constantZero constantZero :=
  Stream.bisim_refl constantZero

/-- The tail of constantZero is bisimilar to constantZero. -/
example : Stream.Bisim (Stream.tail constantZero) constantZero :=
  fun _ => rfl

end LeanFX2.Codata
