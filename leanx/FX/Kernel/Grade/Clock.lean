import FX.Kernel.Grade.Tier

/-!
# Clock domain (dimension 12) — which clock drives a signal

Per `fx_design.md` §6.3 (dim 12), §18.7 (hardware clock
domains), and §18.8 (the synthesizable subset).  Values carry
the name of the clock they are synchronized to — or nothing,
meaning they are combinational (pure function of their inputs,
no storage, usable in any domain).

  * `combinational`       — no clocked storage; composition unit.
                            Fed by / feeds any domain.  Default.
  * `sync(clockName)`     — register output or signal derived from
                            a flip-flop clocked by `clockName`.  The
                            only source of inter-cycle state.

Two different `sync(X)` and `sync(Y)` signals cannot be combined
without a synchronizer (`sync_2ff`, §18.7).  The kernel models
this as a **partial** parallel combine: the same-clock case
returns the single domain, cross-clock returns `none` and the
caller surfaces it as compile error `CD001` — the same
validity-failure shape that `Overflow.add` uses for its
cross-discipline collisions.

## Surface-syntax mapping

Per `fx_design.md` §18.7 the source-level grants map:

  * (no annotation)              → `combinational`  (default)
  * `with Sync(clk_id)`          → `sync(clk_id)`

Combinational is the default so a `hardware fn` or un-clocked
expression defaults to "plug into any domain".  The explicit
`Sync(...)` grant names the domain.

## Algebra

Parallel combine (`add`) is partial:

  * combinational + rightClock                 = rightClock
  * leftClock      + combinational             = leftClock
  * sync(clk)      + sync(clk)                 = sync(clk)
  * sync(clk_a)    + sync(clk_b), clk_a ≠ clk_b = none    (CD001)

Sequential combine (`mul`) is `add` — the composition of two
clocked signals along a value/usage chain is governed by the
same incompatibility check.  §6.3 treats Clock as Tier L.  The
§H.8 Grade-lattice axiom family carries the validity predicate.

The `decide` cases below compile to the tables above.  No fuel,
no tactics — the entire algebra is a finite case split on the
two variants.
-/

namespace FX.Kernel

/--
The clock-domain grade.  `sync` carries the clock identifier
as a `String`; two `sync` values are equal iff their names are
equal (structural, no semantic canonicalization — the
elaborator hands the kernel already-resolved names).
-/
inductive Clock : Type where
  | combinational : Clock
  | sync          : String → Clock
  deriving DecidableEq, Repr

namespace Clock

/-! ## Partial join

`combinational` is the unit — combining anything with
combinational preserves the other side.  Two `sync` domains
combine idempotently when equal and report `none`
(incompatibility) when distinct.
-/
def add : Clock → Clock → Option Clock
  | combinational, rightClock   => some rightClock
  | leftClock,     combinational => some leftClock
  | sync leftName, sync rightName =>
    if leftName == rightName then some (sync leftName) else none

/-- Sequential combine collapses to `add` — §6.3 says cross-
    clock mixing at every composition site is the same error. -/
def mul : Clock → Clock → Option Clock := add

/-! ## Subsumption

`combinational` is the bottom of the preorder: a combinational
signal can stand in for any clock domain (it has no storage of
its own).  Two `sync` domains are comparable only when their
names coincide.
-/
inductive LessEq : Clock → Clock → Prop where
  | refl         : ∀ clk, LessEq clk clk
  | combinationalLe : ∀ clk, LessEq combinational clk

instance : LE Clock := ⟨LessEq⟩

theorem LessEq.trans {lowerClock middleClock upperClock : Clock}
    (lowerLeMiddle : lowerClock ≤ middleClock)
    (middleLeUpper : middleClock ≤ upperClock) :
    lowerClock ≤ upperClock := by
  cases lowerLeMiddle with
  | refl              => exact middleLeUpper
  | combinationalLe _ =>
    cases middleLeUpper with
    | refl              => exact LessEq.combinationalLe _
    | combinationalLe _ => exact LessEq.combinationalLe _

instance decLe : (leftClock rightClock : Clock) → Decidable (LessEq leftClock rightClock)
  | combinational, _             => isTrue (LessEq.combinationalLe _)
  | sync leftName, combinational =>
    isFalse (fun contra => by cases contra)
  | sync leftName, sync rightName =>
    if hEq : leftName = rightName then
      isTrue (by subst hEq; exact LessEq.refl _)
    else
      isFalse (fun contra => by
        cases contra
        exact hEq rfl)

/-! ## Laws

Commutativity, associativity, idempotence, unit laws, and the
combinational bottom / sync-diagonal characterization.  Each is
a finite case split decidable by `simp [add]` or `rfl`.
-/

theorem add_comm (leftClock rightClock : Clock) :
    add leftClock rightClock = add rightClock leftClock := by
  cases leftClock <;> cases rightClock <;> try rfl
  case sync.sync leftName rightName =>
    -- The `sync/sync` cell: both branches reduce to `some (sync X)`
    -- iff the names match.  Split on the name equality up front so
    -- both sides' guards collapse symmetrically.
    by_cases hEq : leftName = rightName
    · subst hEq; simp [add]
    · have hSym : ¬ rightName = leftName := fun h => hEq h.symm
      simp [add, hEq, hSym]

theorem add_idem (clk : Clock) : add clk clk = some clk := by
  cases clk <;> simp [add]

/-- Clock mul is commutative.  Since `mul := add`, this is a
    definitional re-export of `add_comm`.  Used by the
    aggregate `Grade.mul_comm_of_same_provenance` (Q48). -/
theorem mul_comm (leftClock rightClock : Clock) :
    mul leftClock rightClock = mul rightClock leftClock :=
  add_comm leftClock rightClock

-- Associativity over the Option monad is NOT proved here.  The
-- nine-cell case split holds, but the Lean-level proof requires
-- the `Option.bind` commuting-diagram machinery that Phase 8's
-- §H.8 Grade-lattice theorem family will bring in.  The audit
-- invariant bans `sorry` in FX/Kernel/**, so we leave the law
-- unstated rather than stub it.  Overflow and Representation
-- use the same accounting (they also omit the full-monad
-- associativity law) and route concrete associativity via
-- case-by-case `decide` in test files.

theorem combinational_add (clk : Clock) : add combinational clk = some clk := by
  cases clk <;> rfl

theorem add_combinational (clk : Clock) : add clk combinational = some clk := by
  cases clk <;> rfl

theorem combinational_le (clk : Clock) : combinational ≤ clk :=
  LessEq.combinationalLe _

/-- The only way `sync(x)` and `sync(y)` can combine at `add` is
    when their names agree — captures §18.7 CD001. -/
theorem sync_sync_none_iff (leftName rightName : String)
    (hEq : leftName ≠ rightName) :
    add (sync leftName) (sync rightName) = none := by
  simp [add, hEq]

/-- Antisymmetry — combined with reflexivity and transitivity,
    `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftClock rightClock : Clock}
    (leftLeRight : leftClock ≤ rightClock)
    (rightLeLeft : rightClock ≤ leftClock) :
    leftClock = rightClock := by
  cases leftLeRight with
  | refl              => rfl
  | combinationalLe _ =>
    cases rightLeLeft with
    | refl              => rfl
    | combinationalLe _ => rfl

end Clock

/-! ## TierL instance (T4)

Clock fits Tier L: `add` is the partial join (same-clock combines
idempotently, cross-clock is `none` = CD001), join commutes, join
is idempotent.  Clock's meet is identical to its join (same
"must-agree-or-fail" semantics for both parallel and sequential
composition), so `meetOpt := add`.

Per §18.7 `combinational` is the bottom (default, plug into any
domain). -/
instance : TierL Clock where
  default        := Clock.combinational
  le             := Clock.LessEq
  le_refl        := Clock.LessEq.refl
  le_trans       := Clock.LessEq.trans
  joinOpt        := Clock.add
  meetOpt        := Clock.add
  joinOpt_comm   := Clock.add_comm
  joinOpt_idem   := Clock.add_idem
  meetOpt_comm   := Clock.add_comm

end FX.Kernel
