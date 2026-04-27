import FX.Kernel.Inductive
import FX.Kernel.Term

/-!
# Derived spec — Machine translation (§13, D8)

Machines are the surface form where FX's capabilities converge:
states with typed data, transitions with guards and effects,
properties the compiler verifies.  Each surface `machine`
declaration translates to an `IndSpec` for the state space
plus one `Π` per transition plus optional LTL / structural
properties discharged via `std/ltl` and `std/machine_props`.

This module documents the translation and pins the expected
shape via `example` blocks.  UNTRUSTED (L3 per SPEC.md §5) —
the load-bearing work lives in `FX/Kernel/Inductive.lean`
(the `IndSpec` structure the state space projects to),
`FX/Kernel/Typing.lean` (Pi-intro / Pi-elim for transitions),
and `FX/Elab/Elaborate.lean` (the machine elaborator lands
with M1 and §13 wiring).

## Surface syntax (§13.1)

```
machine ConnectionState
  state Disconnected;
  state Connecting of { host: string; attempt: nat };
  state Connected  of { socket: socket_handle };
  state Error      of { last_error: connect_error; retries: nat };

  transition connect : Disconnected -> Connecting
    requires valid_host(host);
  transition established : Connecting -> Connected;
  transition retry : Connecting -> Connecting
    requires attempt < MAX_RETRIES;
    ensures new.attempt == old.attempt + 1;
  transition fail : Connecting -> Error;
  transition recover : Error -> Connecting
    requires retries < MAX_RETRIES;
  transition close : Connected -> Disconnected;

  initial  Disconnected;
  terminal Disconnected;
end machine;
```

Calling a transition invalid from the current state is a
compile error — the kernel's Pi-elim refines the state
ctor through the transition's source-refinement.

## Translation to kernel (§31.7 pattern)

**Step 1 — state space as `IndSpec`.**  Each surface
`machine M` produces one `IndSpec` whose ctors are the
declared states.  Stateless states are nullary ctors;
stateful states carry their payload as ctor args.

For `ConnectionState` above, the translation yields:

```
IndSpec {
  name := "ConnectionState"
  params := []
  ctors  := [
    { name := "Disconnected", args := [], argNames := [] },
    { name := "Connecting",
      args     := [string, nat],
      argNames := ["host", "attempt"] },
    { name := "Connected",
      args     := [socket_handle],
      argNames := ["socket"] },
    { name := "Error",
      args     := [connect_error, nat],
      argNames := ["last_error", "retries"] }
  ]
}
```

**Step 2 — transitions as `Π` functions with state-refined
source.**  Each `transition t : S₁ -> S₂` elaborates to a
Pi of shape:

```
t : Π (s :_1 ConnectionState { s is S₁ }) (args...)
      → ConnectionState { result is S₂ } at effects
```

The `{ s is S₁ }` refinement narrows the input's ctor tag;
the kernel's refinement + usage grade machinery verifies
that callers only fire `t` from a valid source state.  The
return refinement `{ result is S₂ }` encodes `ensures` on
the destination shape.

**Step 3 — initial and terminal as invariants.**  `initial
Disconnected;` declares `Disconnected` as the canonical
entry point; `terminal Disconnected;` requires every legal
path to end at `Disconnected`.  Both check at elaboration
against the transition graph reachability.

## Transition modifiers (§13.2)

Each modifier lifts to a specific kernel addition:

  * **`requires P`** — predicate added to the transition Pi's
    precondition via §10 refinement; SMT discharges at each
    call site.
  * **`ensures Q`** — predicate on the returned state; part of
    the Pi's refined return type.
  * **`with E`** — effect row on the transition Pi's return-
    effect field.
  * **`inverse t'`** — paired transition declared at the same
    site; compiler proves `t ; t' = id` via §10 SMT over the
    state payload.  Used for compensation chains (§13.3).
  * **`timeout d -> S`** — time-triggered fallback transition;
    `after d` desugars to a guard on a scheduler-managed
    timer.  Logical-tick semantics per §13.15.
  * **`retry n strategy`** — repeated attempt sugar; translates
    to a bounded loop over the transition Pi.
  * **`atomic`** — all-or-nothing; the transition's body is
    single-step at the kernel level (one Pi call, no partial
    state visible).
  * **`idempotent(key: k)`** — safe-to-repeat; compiler proves
    repeated application with same `k` returns the same state.
  * **`commutative`** — order-independent; compiler proves
    `t₁ ; t₂ = t₂ ; t₁` on disjoint state components.
  * **`monotonic`** — forward-only in a declared partial
    order over the state fields.
  * **`emits Event(data)`** — transition produces an event on
    an output channel; translates to a `Send` at a linked
    session channel (§11.16 higher-order sessions).
  * **`on_fail mode`** — failure behavior: `Recoverable =>
    stay`, `Critical => goto Error`, `Atomic => rollback`.
    Recoverable is default for pure transitions; effectful
    transitions require explicit `on_fail`.

## Composition (§13.4)

Six operations combine machines.  Each produces a new
`IndSpec` + transition set per well-defined algebraic rules.

  * **Product (`M₁ * M₂`)** — parallel independent.  State is
    the Sigma of component states; transitions interleave.
    IndSpec is the product of component specs.
  * **Synchronized product (`M₁ *sync(e₁,…) M₂`)** — parallel
    with named sync events; synchronized transitions fire
    together on all synchronized machines.
  * **Sequence (`M₁ >> M₂`)** — one then another.  M₁'s
    terminal data feeds M₂'s initial data via kernel Pi
    composition.  The elaborator chains the two IndSpecs'
    terminal/initial ctors.
  * **Choice (`match c; Red => M₁; Blue => M₂; end match`)** —
    one of several; choice is external to the inner machines.
  * **Loop (`M *{ while cond }`)** — repeat until `cond`
    false.  Needs §10.2 `decreases` or `with Div`.
  * **Nest** — hierarchical.  Outer state's payload includes
    inner machine's IndSpec value.  Nested state payload
    telescopes through the outer IndSpec's ctor args.

## Properties (§13.5)

Machine properties are ordinary `assert`s over the machine's
execution trace (a sized codata stream per §11.15 + §3.5).
Four LTL primitives imported from `std/ltl`:

  * `G<M>(φ)` — globally φ
  * `F<M>(φ)` — finally φ
  * `X<M>(φ)` — next step φ
  * `φ U ψ`   — strong until

Structural predicates from `std/machine_props`:

  * `deadlock_free(m)` — every reachable state has at least
    one enabled transition (or is terminal)
  * `deterministic(m)` — for every (state, transition), at
    most one valid next state
  * `reachable(m, s)` — s reachable from initial
  * `bounded_size(m, n)` — total state count ≤ n

Decidability table (§13.5):

```
Machine shape                        Discharge mechanism
────────────────────────────────    ───────────────────────
finite states                        Vardi-Wolper Büchi
                                     automaton product
parameterized, comptime-bounded      comptime unrolling
parameterized @[cutoff(n)]           symmetry reduction
                                     (Emerson-Kahlon 2003)
infinite state + user invariant      user `assert always I;`
                                     + SMT discharge
infinite state, no invariant         REJECTED (M020)
```

## Parameterized machines (§13.9)

```
machine Queue<a: type, depth: nat>
  where depth > 0 and is_power_of_2(depth);

  state Empty;
  state Partial of { items: array(a, depth); count: nat { count < depth } };
  state Full    of { items: array(a, depth) };

  transition enqueue : (Empty | Partial) -> (Partial | Full)
    requires state is not Full;
  transition dequeue : (Partial | Full) -> (Empty | Partial)
    requires state is not Empty;

  initial Empty;
end machine;
```

Type parameters on the surface `machine` project into the
elaborated `IndSpec.params`; value parameters (like `depth`)
must be `comptime`-evaluable and appear as refined kernel
values in the ctor arg types.

## Inverse transitions (§13.3)

```
machine BankTransfer
  transition debit : Initiated -> Debited with IO
    ensures from.balance == old.from.balance - amount;
    inverse restore_debit : Debited -> Initiated
      ensures from.balance == old.from.balance + amount;
  ...
end machine;
```

Inverse pairs generate compensation chains: the elaborator
proves `debit ; restore_debit = id` via §10 SMT on the
balance arithmetic.  On runtime failure, the compensation
chain is derived mechanically from the inverse declarations.

## Actor integration (§13.14)

Each `actor` is a machine processing typed messages.  The
compiler verifies exhaustive `(message, state)` coverage:

```
actor UserSession
  machine State
    state LoggedOut;
    state LoggedIn of { user: user; last_active: timestamp };
  end machine;

  receive Login(credentials) when LoggedOut => login(credentials);
  receive Request(data)      when LoggedIn  => handle_request(data);
  -- compile error if any (message × state) pair is unhandled
end actor;
```

## Refinement (§13.6)

When a specification machine `MS` and implementation machine
`MI` exist, `refinement r MI refines MS via ...` registers a
state-mapping function `MI.state → MS.state`; the elaborator
proves every `MI` path projects to a valid `MS` path.  Used
for hardware verification (ISA vs pipeline, §18.12) and
compiler/protocol verification.

## Deferred — surface machine decl elaboration (E010)

`machine M ... end machine;` is parsed by `Parser.parseDecl`
per fx_grammar.md §10, but `elabDecl` rejects it at E010
(`machine declarations are not yet supported`).  Landing
path (M3 milestone and §13 surface wiring):

  1. Extend `elabTypeDeclSpec` with a `machine` branch:
     - Build `IndSpec` from the state list (one ctor per
       state, payload fields → ctor args).
     - Build one `Π` per transition with state-refined
       source + destination.
     - Check initial/terminal reachability via transition
       graph BFS at elaboration.
     - Register per-machine property `assert`s as proof
       obligations (discharged by SMT or mCRL2).
  2. Wire `@[event_sourced]` code generation (§13.23).
  3. Add LTL primitives to std/ltl prelude.
  4. Add machine-state snapshots (§13.20) + atomic chains.
  5. Implement machine transformers (§13.12 —
     intercept/guard/monitor/restrict/extend).

Each step composable with the existing IndSpec + Pi
infrastructure; no new kernel axiom required.  Machines
are a derived surface form per §H.12.
-/

namespace FX.Derived.Machine

open FX.Kernel

/-! ## Simple stateless machine — traffic light

```
machine TrafficLight
  state Red;
  state Yellow;
  state Green;

  transition go    : Red    -> Green;
  transition slow  : Green  -> Yellow;
  transition stop  : Yellow -> Red;

  initial Red;
end machine;
```

Three nullary states, three transitions, no payload.  Pins
the simplest possible machine shape. -/

/-- Kernel state-space IndSpec for TrafficLight.  No type
    params, three nullary ctors.  Matches what the machine
    elaborator produces on the surface above. -/
def trafficLightSpec : IndSpec :=
  { name   := "TrafficLight"
  , params := []
  , ctors  := [
      { name := "Red",    args := [] },
      { name := "Yellow", args := [] },
      { name := "Green",  args := [] }
    ]
  }

example : trafficLightSpec.ctorCount = 3 := by decide
example : trafficLightSpec.paramCount = 0 := by decide
example : trafficLightSpec.ctors.map (·.name) =
    ["Red", "Yellow", "Green"] := by decide

-- Each state looks up by name at its declaration index.
example : (trafficLightSpec.findCtor? "Red").map    Prod.fst = some 0 := by decide
example : (trafficLightSpec.findCtor? "Yellow").map Prod.fst = some 1 := by decide
example : (trafficLightSpec.findCtor? "Green").map  Prod.fst = some 2 := by decide
example : trafficLightSpec.findCtor? "Purple"                 = none   := by decide

/-- Kernel shape for the `go` transition — a Pi from a
    `TrafficLight { s is Red }` state to a
    `TrafficLight { s is Green }` state.  Phase-2 elides the
    refinement narrowing; the full form lands with M3.  The
    Pi's return effect is Tot (pure transition). -/
def goTransitionShape : Term :=
  Term.pi Grade.default
    (Term.ind "TrafficLight" [])   -- source state (refined to Red)
    (Term.ind "TrafficLight" [])   -- target state (refined to Green)
    Effect.tot

-- Transition is a Pi producing a state — structurally a Pi
-- with the state IndSpec on both sides.
example : (fun t => match t with
    | .pi _ _ _ _ => true
    | _           => false) goTransitionShape = true := by native_decide

/-! ## Stateful machine — ConnectionState (§13.1)

The canonical example from §13.1: four states, two carry
payload data.  Pins that stateful ctors produce IndCtors
with `args` carrying the payload types and `argNames`
recording the declared field names. -/

/-- Kernel IndSpec for ConnectionState.  Disconnected is
    nullary; Connecting has two args (host, attempt);
    Connected has one (socket); Error has two (last_error,
    retries).  Phase-2 the payload types are placeholder
    inductives — a real elaboration would use the concrete
    surface types (`string`, `nat`, `socket_handle`,
    `connect_error`).  `argNames` record the surface field
    names for Phase-2's pretty-printing + field lookups. -/
def connectionStateSpec : IndSpec :=
  { name   := "ConnectionState"
  , params := []
  , ctors  := [
      { name := "Disconnected", args := [] },
      { name     := "Connecting"
        args     := [Term.ind "string" [], Term.ind "Nat" []]
        argNames := ["host", "attempt"] },
      { name     := "Connected"
        args     := [Term.ind "socket_handle" []]
        argNames := ["socket"] },
      { name     := "Error"
        args     := [Term.ind "connect_error" [], Term.ind "Nat" []]
        argNames := ["last_error", "retries"] }
    ]
  }

example : connectionStateSpec.ctorCount = 4 := by decide

-- Disconnected is nullary — no payload args.
example : (connectionStateSpec.ctorAt? 0).map (·.args.length) = some 0 := by decide

-- Connecting carries two fields, named host and attempt.
example : (connectionStateSpec.ctorAt? 1).map (·.args.length) = some 2 := by decide
example : (connectionStateSpec.ctorAt? 1).map (·.argNames) =
    some ["host", "attempt"] := by decide

-- Field-index lookup drives the elaborator's dot-access:
-- `conn.attempt` when conn : Connecting resolves to index 1.
example :
    (connectionStateSpec.ctorAt? 1).bind (fun ctor =>
      ctor.argNames.idxOf? "attempt") = some 1 := by native_decide

-- Connected carries one field (the socket handle).
example : (connectionStateSpec.ctorAt? 2).map (·.args.length) = some 1 := by decide
example : (connectionStateSpec.ctorAt? 2).map (·.argNames) =
    some ["socket"] := by decide

-- Error carries two fields.
example : (connectionStateSpec.ctorAt? 3).map (·.args.length) = some 2 := by decide

/-! ## Parameterized machine — Queue<a, depth> (§13.9)

The canonical bounded-queue example.  One type parameter
`a: type`, one value parameter `depth: nat`.  State ctors
may reference the type param via de Bruijn index 0 in the
ctor-arg scope — parallel to how `option<a>` does for its
`Some(a)` ctor (§3.3). -/

/-- Kernel shape for a single-param Queue machine.  States:
    Empty (nullary), Partial (carries two fields referencing
    param `a`), Full (one field).  The `args` use `Term.var 0`
    to reference the spec's sole type param. -/
def queueMachineSpec : IndSpec :=
  { name   := "Queue"
  , params := [Term.type Level.zero]
  , ctors  := [
      { name := "Empty", args := [] },
      { name     := "Partial"
        args     := [Term.var 0, Term.ind "Nat" []]
        argNames := ["items", "count"] },
      { name     := "Full"
        args     := [Term.var 0]
        argNames := ["items"] }
    ]
  }

example : queueMachineSpec.ctorCount = 3   := by decide
example : queueMachineSpec.paramCount = 1  := by decide

-- Partial's first arg references the type param via var 0.
example :
    (queueMachineSpec.ctorAt? 1 |>.bind (·.args.head?) |>.map
      (fun t => match t with | .var i => i | _ => 999))
      = some 0 := by decide

/-! ## Transition Pi shape — Connecting -> Connected

The `established` transition of ConnectionState.  Kernel
shape: Pi from ConnectionState refined to Connecting, to
ConnectionState refined to Connected, with IO effect per
the canonical declaration. -/

/-- Canonical Pi shape for a transition carrying IO.  A
    full elaboration refines both states via §10 predicates;
    Phase-2 uses the bare ConnectionState IndSpec.  A
    regression that dropped the IO effect or swapped the
    argument/return Pi shape surfaces at this definition. -/
def establishedTransition : Term :=
  Term.pi Grade.default
    (Term.ind "ConnectionState" [])   -- refined to Connecting
    (Term.ind "ConnectionState" [])   -- refined to Connected
    Effect.io_

-- Established transition has IO effect on its return.
example :
    (fun t => match t with
      | .pi _ _ _ eff => eff.io
      | _             => false) establishedTransition = true := by
  native_decide

/-- A Tot transition — `go` in TrafficLight has no effect. -/
def goTransition : Term :=
  Term.pi Grade.default
    (Term.ind "TrafficLight" [])
    (Term.ind "TrafficLight" [])
    Effect.tot

example :
    (fun t => match t with
      | .pi _ _ _ eff => eff.io
      | _             => true) goTransition = false := by
  native_decide

/-! ## Nullary-state enumeration — initial/terminal check

Machines with only nullary states (enum machines like
TrafficLight) reduce to plain ADTs under the hood.  The
machine-specific machinery only adds the transition-graph
invariants (initial / terminal / reachability).  An enum
machine's IndSpec is structurally identical to an ADT's
IndSpec (§3.3 D4) — pinning this identity is a regression
witness against a future refactor that accidentally
divergences enum-machine translation from ADT translation. -/

/-- The three-state enum from §3.3 is identical to the
    TrafficLight machine's state space modulo naming.  Both
    produce nullary-ctor IndSpecs with no params. -/
def colorSpec : IndSpec :=
  { name   := "color"
  , params := []
  , ctors  := [
      { name := "Red",   args := [] },
      { name := "Green", args := [] },
      { name := "Blue",  args := [] }
    ]
  }

-- Both enum-machine and ADT IndSpecs have the same
-- structural shape (nullary ctors, no params).
example : colorSpec.paramCount = trafficLightSpec.paramCount := by decide
example : colorSpec.ctorCount  = trafficLightSpec.ctorCount  := by decide
example : (colorSpec.ctors.map (·.args.length)) =
          (trafficLightSpec.ctors.map (·.args.length)) := by decide

/-! ## Two-ctor machine with mixed payload — actor-style

An actor's State machine often has two states: a stateless
one (awaiting input) and a stateful one (processing with
captured data).  This shape tests that `findCtor?` picks the
right ctor index even when payload shape varies across
ctors. -/

/-- Actor-like state machine with LoggedOut (nullary) and
    LoggedIn (carries user + timestamp). -/
def userSessionSpec : IndSpec :=
  { name   := "UserSession"
  , params := []
  , ctors  := [
      { name := "LoggedOut", args := [] },
      { name     := "LoggedIn"
        args     := [Term.ind "user" [], Term.ind "timestamp" []]
        argNames := ["user", "last_active"] }
    ]
  }

example : userSessionSpec.ctorCount = 2 := by decide
example : (userSessionSpec.findCtor? "LoggedOut").map Prod.fst =
    some 0 := by decide
example : (userSessionSpec.findCtor? "LoggedIn").map Prod.fst =
    some 1 := by decide

-- Mixed shape: LoggedOut has 0 fields, LoggedIn has 2.
example :
    userSessionSpec.ctors.map (·.args.length) = [0, 2] := by decide

/-! ## Registry status

Machine declarations arrive with M3 (§13 wiring) and do not
populate `Inductive.specByName?` until then.  The examples
above build `IndSpec` values directly; they are NOT yet
threaded into the elaboration-time spec registry.  Surface
`machine M ... end machine;` at elaboration time falls
through to E010 (`machine declarations are not yet
supported`). -/

example : Inductive.specByName? "TrafficLight"    = none := rfl
example : Inductive.specByName? "ConnectionState" = none := rfl
example : Inductive.specByName? "Queue"           = none := rfl
example : Inductive.specByName? "UserSession"     = none := rfl

end FX.Derived.Machine
