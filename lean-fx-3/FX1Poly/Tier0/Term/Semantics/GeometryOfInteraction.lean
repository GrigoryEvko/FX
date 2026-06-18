/-! # Tier0/Term — geometry of interaction: the token machine (term-23)

The third term-axis SEMANTICS rung.  Geometry of Interaction (Girard) reads computation DYNAMICALLY: a
TOKEN travels through an interaction network and its trajectory — the EXECUTION — IS cut-elimination run as
a machine (the "particle-style" / token-machine presentation, Danos-Regnier, Mackie).  This file ships the
operational core (each piece zero-axiom, Init-only):

  * **`TokenMachine`** — a configuration space with a DETERMINISTIC partial step (`step : Config →
    Option Config`; `none` = the token has reached the boundary / exited).  Determinism is structural:
    `step_deterministic`.
  * **`execute`** — fuel-bounded run-to-halt, with `IsHalted` (`step = none`) and the absorption laws
    `execute_halted` (a halted config is fixed) and `execute_succ_of_halted` / `reaches_stable` (once the
    trajectory reaches the boundary, more fuel changes nothing).
  * **`Reaches`** + **`reaches_unique`** (★) — the EXECUTION IS DETERMINATE: a starting configuration
    reaches at most one exit configuration, so the token machine computes a well-defined partial function —
    the GoI denotation.
  * **`wireMachine`** + **`wireMachine_reachesExit`** — a concrete witness: the token traverses a length-`p`
    WIRE and exits at the boundary (the GoI reading of an axiom link / identity).

## Honest scope

Shipped: the deterministic token machine, fuel-bounded execution with the absorption/stability laws, the
DETERMINACY of execution (`reaches_unique`), and the wire-traversal witness.  DEFERRED: the GoI SOUNDNESS
theorem (execution is INVARIANT under cut-elimination — running the token across a cut equals running it on
the cut-eliminated network, the "execution = normalization" correspondence), the TRACE / feedback
composition of networks (the geometry-of-interaction situation), and Girard's operator-algebra GoI (the
execution formula `(1 - σ)⁻¹` in a C*-algebra).  This is the `term-23` slice of the omnibus
`fxTerm_hasDenotationalAdequacy = false`.

## Zero-axiom verification

`execute` is structural Nat recursion; the absorption laws are induction on fuel with the start reverted,
reducing the one-step peel by `cases` on `step`; `reaches_unique` splits on `Nat.le_total` and rebuilds the
larger run via `reaches_stable` (right-additive fuel, so only the definitional `n + (k+1) = (n+k)+1`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTier0TermGeometryOfInteraction.lean`.
-/

namespace FX1Poly.Core

/-! ## The token machine -/

/-- A **token machine**: a configuration space with a deterministic partial transition.  `step c = none`
means the token has reached the boundary (exited); `step c = some c'` is the next position. -/
structure TokenMachine where
  /-- Token configurations (position + direction + stack, abstractly). -/
  Config : Type
  /-- The deterministic one-step transition; `none` = exited. -/
  step : Config → Option Config

/-- The token machine is DETERMINISTIC: a configuration has at most one successor. -/
theorem TokenMachine.step_deterministic (machine : TokenMachine) {config first second : machine.Config}
    (toFirst : machine.step config = some first) (toSecond : machine.step config = some second) :
    first = second :=
  Option.some.inj (toFirst ▸ toSecond)

/-- A configuration is **halted** when the token has exited. -/
def TokenMachine.IsHalted (machine : TokenMachine) (config : machine.Config) : Prop :=
  machine.step config = none

/-- **Execution**: run the token for at most `fuel` steps, stopping when it exits. -/
def TokenMachine.execute (machine : TokenMachine) : Nat → machine.Config → machine.Config
  | 0, config => config
  | fuel + 1, config =>
      match machine.step config with
      | none => config
      | some next => machine.execute fuel next

/-- The one-step unfolding of `execute` (definitional). -/
theorem TokenMachine.execute_succ (machine : TokenMachine) (fuel : Nat) (config : machine.Config) :
    machine.execute (fuel + 1) config =
      match machine.step config with
      | none => config
      | some next => machine.execute fuel next := rfl

/-- A halted configuration is a FIXED POINT of execution. -/
theorem TokenMachine.execute_halted (machine : TokenMachine) {config : machine.Config}
    (halted : machine.IsHalted config) : ∀ fuel, machine.execute fuel config = config := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ previous =>
      rw [machine.execute_succ previous config, halted]

/-- Reaching a halted result is STABLE under one extra unit of fuel (halting is absorbing). -/
theorem TokenMachine.execute_succ_of_halted (machine : TokenMachine) {result : machine.Config}
    (halted : machine.IsHalted result) :
    ∀ (fuel : Nat) {start : machine.Config}, machine.execute fuel start = result →
      machine.execute (fuel + 1) start = result := by
  intro fuel
  induction fuel with
  | zero =>
      intro start reached
      have startEqResult : start = result := reached
      rw [machine.execute_succ 0 start, startEqResult, halted]
  | succ previous inductionHypothesis =>
      intro start reached
      rw [machine.execute_succ (previous + 1) start]
      rw [machine.execute_succ previous start] at reached
      cases hstep : machine.step start with
      | none =>
          rw [hstep] at reached
          exact reached
      | some next =>
          rw [hstep] at reached
          exact inductionHypothesis reached

/-- The execution relation: `start` reaches the halted `result`. -/
def TokenMachine.Reaches (machine : TokenMachine) (start result : machine.Config) : Prop :=
  ∃ fuel, machine.execute fuel start = result ∧ machine.IsHalted result

/-- Once the trajectory reaches a halted result, ANY extra fuel keeps it (right-additive stability). -/
theorem TokenMachine.reaches_stable (machine : TokenMachine) {result : machine.Config}
    (halted : machine.IsHalted result) {fuel : Nat} {start : machine.Config}
    (reached : machine.execute fuel start = result) :
    ∀ extra, machine.execute (fuel + extra) start = result := by
  intro extra
  induction extra with
  | zero => exact reached
  | succ previous inductionHypothesis =>
      exact machine.execute_succ_of_halted halted (fuel + previous) inductionHypothesis

/-- ★ **Execution is DETERMINATE**: a configuration reaches at most one exit, so the token machine computes
a well-defined partial function — the GoI denotation. -/
theorem TokenMachine.reaches_unique (machine : TokenMachine) {start firstResult secondResult : machine.Config}
    (toFirst : machine.Reaches start firstResult) (toSecond : machine.Reaches start secondResult) :
    firstResult = secondResult := by
  obtain ⟨firstFuel, firstReached, firstHalted⟩ := toFirst
  obtain ⟨secondFuel, secondReached, secondHalted⟩ := toSecond
  rcases Nat.le_total firstFuel secondFuel with firstLe | secondLe
  · obtain ⟨gap, gapEq⟩ := Nat.le.dest firstLe
    have bridged : machine.execute secondFuel start = firstResult := by
      rw [← gapEq]; exact machine.reaches_stable firstHalted firstReached gap
    rw [secondReached] at bridged
    exact bridged.symm
  · obtain ⟨gap, gapEq⟩ := Nat.le.dest secondLe
    have bridged : machine.execute firstFuel start = secondResult := by
      rw [← gapEq]; exact machine.reaches_stable secondHalted secondReached gap
    rw [firstReached] at bridged
    exact bridged

/-! ## A concrete witness — the wire (axiom link) -/

/-- The **wire** token machine: positions count down to the boundary `0`. -/
def wireMachine : TokenMachine where
  Config := Nat
  step := fun position =>
    match position with
    | 0 => none
    | next + 1 => some next

/-- The exit `0` is halted. -/
theorem wireMachine_isHalted_zero : wireMachine.IsHalted (0 : Nat) := rfl

/-- From position `p`, exactly `p` steps reach the exit. -/
theorem wireMachine_runsToExit : ∀ position : Nat, wireMachine.execute position position = (0 : Nat) := by
  intro position
  induction position with
  | zero => rfl
  | succ previous inductionHypothesis =>
      show wireMachine.execute previous previous = (0 : Nat)
      exact inductionHypothesis

/-- ★ The token traverses the length-`p` wire and EXITS at the boundary — the GoI reading of an axiom
link / the identity. -/
theorem wireMachine_reachesExit (position : Nat) : wireMachine.Reaches position (0 : Nat) :=
  ⟨position, wireMachine_runsToExit position, wireMachine_isHalted_zero⟩

end FX1Poly.Core
