import FX.Kernel.Grade.Tier

/-!
# Protocol (dimension 6) — session-type state

Per `fx_design.md` §6.3 (dim 6), §11 (session types), and
Appendix A-table row 6.  Tier T in the spec.

## The two-element Phase-1 carrier

A full session-type state is a tree of `send(T).S`,
`receive(T).S`, `branch { S1 | S2 | ... }`, `rec X. S`, and
`end` per §11.1.  The kernel-level GRADE, however, doesn't need
the full tree — the elaborator (or a future Protocol-aware
typing layer) tracks precise state.  What the kernel enforces
via the grade algebra is the coarser property: **is the channel
still in use, or has it been terminated?**

Two carrier elements:

  * `consumed` — the session has reached `end`; the channel
    binding is exhausted.  Grade `0` in §6.3's description.
  * `active`   — the session is mid-protocol; one or more
    steps remain.  Grade `1`-or-higher in §6.3's description.

A fuller Phase-2+ carrier will embed the actual session type
(or at least the step index) so session divergence between
branches becomes a kernel-level check.  Adding that refinement
is backward-compatible: `consumed` becomes the specific
`session end` state, `active` becomes a structured-state
family.

## Algebra — partial add and mul

`add` (parallel combine, e.g., two arms of an `if` sharing a
channel binding) **requires both arms to leave the channel in
the same state**.  Mixed combinations (`consumed + active`) are
**invalid** — one arm consumed the channel, the other didn't —
and return `none` in the `Option Protocol` lifting.  This
mirrors Clock/Overflow/Representation's Tier-L partial
pattern.

`mul` (sequential combine, e.g., using a channel then using the
result) behaves the same as `add` for the coarse Phase-1
carrier: consistent states compose, mixed states are invalid.

  * add (active)   (active)   = some active
  * add (consumed) (consumed) = some consumed
  * add _          _          = none      (mixed → session-state
                                             divergence error)

## Subsumption

At Phase 1 the preorder is just reflexivity: each carrier
element is `≤` only itself.  There is no meaningful "more
active subsumes less active" rule at the coarse granularity —
the two elements describe genuinely different protocol
lifetimes.  `decLe` decides `LessEq` by carrier-element
equality.

## Error code

A kernel site encountering `none` from `Protocol.add`/`mul`
should report `S004` ("session state divergence across parallel
arms") or `S005` ("channel used after termination").  The
exact code depends on whether the failure came from parallel
combine (`add`) or sequential (`mul`) — disambiguation
reserved for the Protocol-aware typing layer.

## Appendix H.8 realization

This file realizes the Tier-T slot of `Grade-semiring-laws` as
a **partial** Phase-1 placeholder.  The full session-type
algebra is Phase-6 work (scope: §26.4 of the Phase-6 design
scope, not yet landed in leanx).
-/

namespace FX.Kernel

/-- Protocol grade — coarse Phase-1 session lifetime state. -/
inductive Protocol : Type where
  /-- Session has reached `end`; channel binding exhausted. -/
  | consumed : Protocol
  /-- Session is mid-protocol; one or more steps remain. -/
  | active   : Protocol
  deriving DecidableEq, Repr

namespace Protocol

/-- Parallel combine — both arms must leave the channel in the
    same state.  Mixed state → `none`. -/
def add : Protocol → Protocol → Option Protocol
  | consumed, consumed => some consumed
  | active,   active   => some active
  | _,        _        => none

/-- Sequential combine — Phase-1 coarse carrier treats this the
    same as parallel combine; mixed state is invalid. -/
def mul : Protocol → Protocol → Option Protocol := add

/-! ## Subsumption

Phase-1 coarse carrier admits only reflexive subsumption.  The
two elements are genuinely incomparable — an `active` channel
cannot stand in for a `consumed` one (the consumer expects no
further operations), nor vice versa.
-/

inductive LessEq : Protocol → Protocol → Prop where
  | refl : ∀ protocol, LessEq protocol protocol

instance : LE Protocol := ⟨LessEq⟩

theorem LessEq.refl' (protocol : Protocol) : protocol ≤ protocol :=
  LessEq.refl protocol

theorem LessEq.trans {lowerProtocol middleProtocol upperProtocol : Protocol}
    (lowerLeMiddle : lowerProtocol ≤ middleProtocol)
    (middleLeUpper : middleProtocol ≤ upperProtocol) :
    lowerProtocol ≤ upperProtocol := by
  cases lowerLeMiddle with
  | refl => exact middleLeUpper

instance decLe : (leftProtocol rightProtocol : Protocol)
    → Decidable (LessEq leftProtocol rightProtocol)
  | consumed, consumed => isTrue (LessEq.refl _)
  | active,   active   => isTrue (LessEq.refl _)
  | consumed, active   => isFalse (fun hLe => by cases hLe)
  | active,   consumed => isFalse (fun hLe => by cases hLe)

/-! ## Laws

The carrier is too small for interesting semiring structure —
no zero element, no distributivity (since `add` is `Option`-
valued, distributivity doesn't apply in the standard form).
What we prove:

  * `add_comm` — parallel combine is commutative.
  * `add_idem` — equal states combine to themselves.
  * `add_same_consumed` / `add_same_active` — concrete
    reductions used by the aggregator.
-/

theorem add_comm (leftProtocol rightProtocol : Protocol) :
    add leftProtocol rightProtocol = add rightProtocol leftProtocol := by
  cases leftProtocol <;> cases rightProtocol <;> rfl

theorem add_idem (protocol : Protocol) : add protocol protocol = some protocol := by
  cases protocol <;> rfl

theorem mul_comm (leftProtocol rightProtocol : Protocol) :
    mul leftProtocol rightProtocol = mul rightProtocol leftProtocol :=
  add_comm leftProtocol rightProtocol

theorem mul_idem (protocol : Protocol) : mul protocol protocol = some protocol :=
  add_idem protocol

theorem add_consumed_consumed : add consumed consumed = some consumed := rfl
theorem add_active_active     : add active   active   = some active   := rfl
theorem add_consumed_active   : add consumed active   = none          := rfl
theorem add_active_consumed   : add active   consumed = none          := rfl

end Protocol

/-! ## TierT instance (T5)

Protocol's Phase-1 `{consumed, active}` carrier fits Tier T's minimal
interface: one partial `combineOpt` operation, no semiring/lattice
laws.  Session-type transitions proper (beyond the coarse lifetime
state) land in Phase-6 per the spec §26.4 scope note; the tier class
doesn't claim them. -/
instance : TierT Protocol where
  default      := Protocol.active
  le           := Protocol.LessEq
  le_refl      := Protocol.LessEq.refl
  le_trans     := Protocol.LessEq.trans
  combineOpt   := Protocol.add

end FX.Kernel
