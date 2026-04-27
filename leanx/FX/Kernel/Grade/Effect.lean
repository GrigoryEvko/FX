import FX.Kernel.Grade.Tier

/-!
# Effect (dimension 4) — built-in effect row

Per `fx_design.md` §6.3 (dim 4) and §9.  Tier S.  A **subset
lattice** over a finite label set.

The design doc uses `+ = * = ∪` for both parallel and sequential
combine (set union).  Under this choice the structure is an
idempotent commutative monoid for both operations with `Tot`
(empty row) as the identity — not a strict semiring with
annihilator, since union has no annihilator.

## Label set and surface-syntax mapping

Eight built-in labels from §9.4.  `Fail` (user exceptions) is an
algebraic effect in §9.5, not a built-in row bit.  Source-level
`with …` rows map one-to-one onto record fields:

  * `with IO`     ↔ `Effect.io    = true`  (arbitrary I/O)
  * `with Div`    ↔ `Effect.div   = true`  (may diverge)
  * `with Ghost`  ↔ `Effect.ghost = true`  (erased at runtime)
  * `with Exn`    ↔ `Effect.exn   = true`  (built-in exception)
  * `with Alloc`  ↔ `Effect.alloc = true`  (may heap-allocate)
  * `with Read`   ↔ `Effect.read  = true`  (may read state)
  * `with Write`  ↔ `Effect.write = true`  (may write state)
  * `with Async`  ↔ `Effect.async = true`  (may await / suspend)

Absence of `with …` (or explicit `with Tot`) is the empty row
`tot`, the additive identity.  Composite rows like
`with IO, Async` elaborate to `add io_ async_`.

## Subeffect `Read ≤ Write`

The rule "Write implies Read" (§9.3 / Appendix B) is a
*structural* property: any source row containing `Write` is
**saturated by elaboration** into a record with both
`write := true` and `read := true` before it ever hits this
algebra.  The singleton helper `write_` below reflects that
discipline directly (it sets `read := true`).

We deliberately do **not** bake the implication into `add`
itself: doing so (via normalization inside `add`) would make
associativity proofs combinatorial without changing any
observable behavior — every elaborator-produced value is
already saturated, so `add` on saturated inputs produces a
saturated output by pure pointwise OR.  The `LessEq read_ write_`
test below witnesses that `read ≤ write` holds *after*
saturation; no algebraic axiom is needed.

## Algebra

  * `add = mul = pointwise or` — idempotent comm monoid
  * `tot` is the identity
  * `LessEq = pointwise implication` — subsumption is subset
  * `LessEq` is a partial order (reflexive, transitive, antisymmetric
    — see `LessEq.antisymm`) via extensional equality of the 8-tuple.
-/

namespace FX.Kernel

/--
The effect row as a record of booleans.  Pointwise boolean
structure keeps the algebra clean.
-/
structure Effect where
  io    : Bool := false
  div   : Bool := false
  ghost : Bool := false
  exn   : Bool := false
  alloc : Bool := false
  read  : Bool := false
  write : Bool := false
  async : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Effect

/-- The empty row — the `Tot` effect (pure & terminating). -/
def tot : Effect := {}

/--
Parallel combine: pointwise bitwise or.  The union of two effect
rows.
-/
def add (leftEffect rightEffect : Effect) : Effect :=
  { io    := leftEffect.io    || rightEffect.io
  , div   := leftEffect.div   || rightEffect.div
  , ghost := leftEffect.ghost || rightEffect.ghost
  , exn   := leftEffect.exn   || rightEffect.exn
  , alloc := leftEffect.alloc || rightEffect.alloc
  , read  := leftEffect.read  || rightEffect.read
  , write := leftEffect.write || rightEffect.write
  , async := leftEffect.async || rightEffect.async }

/-- Sequential combine — same union. -/
def mul : Effect → Effect → Effect := add

/-- Subsumption: every label in `a` is also in `b`. -/
def LessEq (smallerEffect largerEffect : Effect) : Prop :=
  (smallerEffect.io    = true → largerEffect.io    = true) ∧
  (smallerEffect.div   = true → largerEffect.div   = true) ∧
  (smallerEffect.ghost = true → largerEffect.ghost = true) ∧
  (smallerEffect.exn   = true → largerEffect.exn   = true) ∧
  (smallerEffect.alloc = true → largerEffect.alloc = true) ∧
  (smallerEffect.read  = true → largerEffect.read  = true) ∧
  (smallerEffect.write = true → largerEffect.write = true) ∧
  (smallerEffect.async = true → largerEffect.async = true)

instance : LE Effect := ⟨LessEq⟩

theorem LessEq.refl (effect : Effect) : effect ≤ effect :=
  ⟨id, id, id, id, id, id, id, id⟩

theorem LessEq.trans {leftEffect midEffect rightEffect : Effect}
    (leftLeMid : leftEffect ≤ midEffect) (midLeRight : midEffect ≤ rightEffect) :
    leftEffect ≤ rightEffect := by
  obtain ⟨ioLow, divLow, ghostLow, exnLow, allocLow, readLow, writeLow, asyncLow⟩ := leftLeMid
  obtain ⟨ioHigh, divHigh, ghostHigh, exnHigh, allocHigh, readHigh, writeHigh, asyncHigh⟩ := midLeRight
  exact ⟨ioHigh ∘ ioLow, divHigh ∘ divLow, ghostHigh ∘ ghostLow, exnHigh ∘ exnLow,
         allocHigh ∘ allocLow, readHigh ∘ readLow, writeHigh ∘ writeLow, asyncHigh ∘ asyncLow⟩

instance decLe (smallerEffect largerEffect : Effect) : Decidable (LessEq smallerEffect largerEffect) := by
  unfold LessEq
  exact inferInstance

/-! ### Idempotent commutative monoid laws -/

theorem add_comm (leftEffect rightEffect : Effect) :
    add leftEffect rightEffect = add rightEffect leftEffect := by
  simp [add, Bool.or_comm]

theorem add_assoc (leftEffect midEffect rightEffect : Effect) :
    add (add leftEffect midEffect) rightEffect
      = add leftEffect (add midEffect rightEffect) := by
  simp [add, Bool.or_assoc]

theorem add_idem (effect : Effect) : add effect effect = effect := by
  simp [add, Bool.or_self]

theorem tot_add (effect : Effect) : add tot effect = effect := by
  simp [add, tot]

theorem add_tot (effect : Effect) : add effect tot = effect := by
  simp [add, tot]

theorem mul_assoc (leftEffect midEffect rightEffect : Effect) :
    mul (mul leftEffect midEffect) rightEffect
      = mul leftEffect (mul midEffect rightEffect) :=
  add_assoc leftEffect midEffect rightEffect

/-- Effect mul is commutative (mul := add; see `Grade.mul`). -/
theorem mul_comm (leftEffect rightEffect : Effect) :
    mul leftEffect rightEffect = mul rightEffect leftEffect :=
  add_comm leftEffect rightEffect

/-! ### Partial-order facts -/

/-- Two-way boolean implication collapses to equality. -/
private theorem bool_iff_eq {leftBool rightBool : Bool}
    (leftImpliesRight : leftBool = true → rightBool = true)
    (rightImpliesLeft : rightBool = true → leftBool = true) : leftBool = rightBool := by
  cases leftBool <;> cases rightBool <;>
    first | rfl | (simp at *) | (cases leftImpliesRight rfl) | (cases rightImpliesLeft rfl)

/--
Antisymmetry: `LessEq` is a genuine partial order on `Effect`.
Combined with `LessEq.refl` and `LessEq.trans` this gives the full
partial-order structure.  Proof: each of the eight bits
satisfies two-way implication, hence each bit is equal, hence
the two records are structurally equal (DecidableEq on the
underlying 8-tuple).
-/
theorem LessEq.antisymm {leftEffect rightEffect : Effect}
    (leftLeRight : leftEffect ≤ rightEffect) (rightLeLeft : rightEffect ≤ leftEffect) :
    leftEffect = rightEffect := by
  obtain ⟨ioFwd, divFwd, ghostFwd, exnFwd, allocFwd, readFwd, writeFwd, asyncFwd⟩ := leftLeRight
  obtain ⟨ioBwd, divBwd, ghostBwd, exnBwd, allocBwd, readBwd, writeBwd, asyncBwd⟩ := rightLeLeft
  have ioEq    := bool_iff_eq ioFwd    ioBwd
  have divEq   := bool_iff_eq divFwd   divBwd
  have ghostEq := bool_iff_eq ghostFwd ghostBwd
  have exnEq   := bool_iff_eq exnFwd   exnBwd
  have allocEq := bool_iff_eq allocFwd allocBwd
  have readEq  := bool_iff_eq readFwd  readBwd
  have writeEq := bool_iff_eq writeFwd writeBwd
  have asyncEq := bool_iff_eq asyncFwd asyncBwd
  cases leftEffect; cases rightEffect
  simp_all

/-- `tot` is the global bottom: every effect row subsumes `tot` from below. -/
theorem tot_le (effect : Effect) : tot ≤ effect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro totHasLabel <;> simp [tot] at totHasLabel

/-!
### Convenience constructors for common effect sets

Each of these is the singleton row for one label.  Use `add` to
combine.  The `write_` form already has `read := true` because
§9.3 makes `Write` imply `Read`; constructing `write_` directly
is the recommended source form.
-/

def io_    : Effect := { io    := true }
def div_   : Effect := { div   := true }
def ghost_ : Effect := { ghost := true }
def exn_   : Effect := { exn   := true }
def alloc_ : Effect := { alloc := true }
def read_  : Effect := { read  := true }
def write_ : Effect := { read  := true, write := true }
def async_ : Effect := { async := true }

/-!
### Surface-name bridge

Maps the eight built-in surface labels of §9.4 to their
singleton records.  Used by the elaborator (A12) to convert a
parsed effect row into the algebraic form checked via `LessEq`.

Write goes through `write_` so the pre-saturation of §9.3
applies: a caller declaring `with Write` implicitly satisfies a
callee using only `with Read`.  Unknown names (user-defined
effects per §9.5 — not yet implemented) return `none`; the
elaborator falls back to a per-name subset check over them.
-/

def fromName? : String → Option Effect
  | "IO"    => some io_
  | "Div"   => some div_
  | "Ghost" => some ghost_
  | "Exn"   => some exn_
  | "Alloc" => some alloc_
  | "Read"  => some read_
  | "Write" => some write_
  | "Async" => some async_
  | _       => none

/-- Parse a surface name list into an algebraic effect row and a
    residual list of unrecognized names.  The two halves are
    checked independently by the A12 enforcement: built-in
    subsumption via `LessEq` (which honors §9.3's `Read ≤ Write`
    via `write_`'s pre-saturation), unknown names via per-name
    subset. -/
def fromNames (names : List String) : Effect × List String :=
  names.foldl (init := (tot, ([] : List String))) fun acc name =>
    let (knownAcc, unknownAcc) := acc
    match fromName? name with
    | some singleton => (add singleton knownAcc, unknownAcc)
    | none           =>
      if unknownAcc.contains name then (knownAcc, unknownAcc)
      else (knownAcc, name :: unknownAcc)

/-- Per-bit difference: names that are `true` in the body row
    and `false` in the declared row.  Used for A12 diagnostics to
    tell the user which specific effects are missing from the
    declared row.  Emits names in spec order (IO, Div, Ghost,
    Exn, Alloc, Read, Write, Async). -/
def wideningNames (bodyEffect declaredEffect : Effect) : List String :=
  let pushWhenWidening (name : String) (bodyBit declaredBit : Bool)
      (acc : List String) : List String :=
    if bodyBit && !declaredBit then acc ++ [name] else acc
  []
    |> pushWhenWidening "IO"    bodyEffect.io    declaredEffect.io
    |> pushWhenWidening "Div"   bodyEffect.div   declaredEffect.div
    |> pushWhenWidening "Ghost" bodyEffect.ghost declaredEffect.ghost
    |> pushWhenWidening "Exn"   bodyEffect.exn   declaredEffect.exn
    |> pushWhenWidening "Alloc" bodyEffect.alloc declaredEffect.alloc
    |> pushWhenWidening "Read"  bodyEffect.read  declaredEffect.read
    |> pushWhenWidening "Write" bodyEffect.write declaredEffect.write
    |> pushWhenWidening "Async" bodyEffect.async declaredEffect.async

/-- Convenience: Bool-valued `LessEq` using the decidable
    instance.  The elaborator prefers this over pattern-matching
    on a `Decidable` proof term. -/
def subsumes (smallerEffect largerEffect : Effect) : Bool :=
  decide (LessEq smallerEffect largerEffect)

end Effect

/-! ## TierSIdem instance (T2)

Effect fits the idempotent join-lattice tier: `add = mul = pointwise or`
on the 8-bit effect tuple, `tot` is the additive identity, and all
three monoid laws (comm, assoc, idem) hold definitionally over the
Boolean algebra.  The strict semiring axiom `zero_mul : mul tot x =
tot` does NOT hold (`mul tot x = add tot x = x`, not `tot`) — which
is why Effect instances `TierSIdem`, not `TierSRing`.

Per §1.2 deny-by-default the carrier's `default` is `tot` (no effects
granted). -/
instance : TierSIdem Effect where
  default      := Effect.tot
  le           := Effect.LessEq
  le_refl      := Effect.LessEq.refl
  le_trans     := Effect.LessEq.trans
  add          := Effect.add
  mul          := Effect.mul
  zero         := Effect.tot
  add_comm     := Effect.add_comm
  add_assoc    := Effect.add_assoc
  add_zero     := Effect.add_tot
  zero_add     := Effect.tot_add
  mul_assoc    := Effect.mul_assoc
  mul_comm     := Effect.mul_comm
  add_idem     := Effect.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel
