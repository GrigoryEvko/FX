/-! # mode-24 — temporal modalities (LTL) over cycle-indexed streams

The temporal modalities `X` (next), `G` (globally), `F` (eventually), `U` (untilOp) as a mode instance, over
CYCLE-INDEXED streams (fx_design §13.18: temporal logic for hardware desugars to quantified properties over
cycle-indexed codata streams — `G φ` ↦ `∀ future, φ`, `F φ` ↦ `∃ future, φ`, `X φ` ↦ `φ` at the next cycle,
`φ U ψ` ↦ the bounded-existence form).

A cycle-indexed stream is modelled as `Nat → State` (time/cycle ↦ state).  A temporal property is a predicate on a
(stream, time) position; the operators are combinators on those predicates.  This rung ships the standard LTL
algebraic laws that hold INTUITIONISTICALLY (zero-axiom, no `Classical.choice`); the laws that genuinely need
classical reasoning (the `¬G ↔ F¬` converse) or a coinductive fixpoint characterization are scoped to markers.

## What this file ships (each piece zero-axiom)

  * `CycleStream` / `TemporalProp` + the boolean combinators (`notOp` / `andOp` / `orOp` / `impliesOp`) and the four
    temporal operators `next` (X), `globally` (G), `eventually` (F), `untilOp` (U).
  * the LTL algebraic laws (intuitionistic):
    - ★ `globally_distrib_and` (`G(φ ∧ ψ) ↔ Gφ ∧ Gψ`), `eventually_distrib_or` (`F(φ ∨ ψ) ↔ Fφ ∨ Fψ`),
      `next_distrib_and` (`X(φ ∧ ψ) ↔ Xφ ∧ Xψ`, by `Iff.rfl` — `X` is self-dual / commutes with everything);
    - `globally_implies_now` (`Gφ → φ`), `now_implies_eventually` (`φ → Fφ`), `globally_implies_eventually` (`Gφ → Fφ`);
    - ★ `untilOp_implies_eventually` (`φ U ψ → Fψ` — untilOp entails eventually);
    - ★ `eventually_not_implies_not_globally` (`F¬φ → ¬Gφ` — the INTUITIONISTIC half of the G/F duality);
    - `globally_idempotent` (`GGφ ↔ Gφ`).

## What is DEFERRED (markers)

  * the CLASSICAL G/F duality converse `¬Gφ → F¬φ` (and `¬Fφ → G¬φ`) — needs `¬∀ → ∃¬`, i.e. `Classical.choice`
    (`hasClassicalTemporalDuality`);
  * the coinductive FIXPOINT characterizations `Fφ ↔ φ ∨ XFφ`, `Gφ ↔ φ ∧ XGφ`, `φUψ ↔ ψ ∨ (φ ∧ X(φUψ))` (the μ/ν
    presentation — needs the successor-shift recursion) (`hasTemporalFixpointLaws`);
  * CTL branching time — the path quantifiers `A`/`E` over computation TREES (here a single linear stream)
    (`hasBranchingTime`);
  * the LTL decision procedure — Büchi automata / bounded model checking decidability over finite-state streams
    (`hasLtlDecisionProcedure`);
  * the kernel hardware temporal operators (§13.18) desugared into the kernel codata streams (cross-axis, `fib`)
    (`hasKernelTemporalFibration`).

Zero external dependencies; raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## Cycle-indexed streams and temporal properties -/

/-- A **cycle-indexed stream**: a state at each cycle / time index. -/
abbrev CycleStream (State : Type) : Type := Nat → State

/-- A **temporal property** — a predicate on a (stream, time) position. -/
abbrev TemporalProp (State : Type) : Type := CycleStream State → Nat → Prop

/-- An atomic temporal property — a state predicate evaluated at the current cycle. -/
def atom {State : Type} (statePredicate : State → Prop) : TemporalProp State :=
  fun stream time => statePredicate (stream time)

/-- Pointwise negation. -/
def notOp {State : Type} (inner : TemporalProp State) : TemporalProp State :=
  fun stream time => ¬ inner stream time

/-- Pointwise conjunction. -/
def andOp {State : Type} (left right : TemporalProp State) : TemporalProp State :=
  fun stream time => left stream time ∧ right stream time

/-- Pointwise disjunction. -/
def orOp {State : Type} (left right : TemporalProp State) : TemporalProp State :=
  fun stream time => left stream time ∨ right stream time

/-- Pointwise implication. -/
def impliesOp {State : Type} (premise conclusion : TemporalProp State) : TemporalProp State :=
  fun stream time => premise stream time → conclusion stream time

/-! ## The temporal operators -/

/-- `X φ` (next) — `φ` holds at the next cycle. -/
def next {State : Type} (inner : TemporalProp State) : TemporalProp State :=
  fun stream time => inner stream (time + 1)

/-- `G φ` (globally) — `φ` holds at every future cycle. -/
def globally {State : Type} (inner : TemporalProp State) : TemporalProp State :=
  fun stream time => ∀ offset : Nat, inner stream (time + offset)

/-- `F φ` (eventually) — `φ` holds at some future cycle. -/
def eventually {State : Type} (inner : TemporalProp State) : TemporalProp State :=
  fun stream time => ∃ offset : Nat, inner stream (time + offset)

/-- `φ U ψ` (untilOp) — `ψ` holds at some future cycle, and `φ` holds at every cycle strictly before it. -/
def untilOp {State : Type} (waiting target : TemporalProp State) : TemporalProp State :=
  fun stream time =>
    ∃ delay : Nat, target stream (time + delay) ∧
      ∀ earlier : Nat, earlier < delay → waiting stream (time + earlier)

/-! ## The LTL algebraic laws (intuitionistic) -/

/-- ★ `G` distributes over `∧`: `G(φ ∧ ψ) ↔ Gφ ∧ Gψ`. -/
theorem globally_distrib_and {State : Type} (firstProp secondProp : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    globally (andOp firstProp secondProp) stream time
      ↔ andOp (globally firstProp) (globally secondProp) stream time := by
  constructor
  · intro everywhereBoth
    exact ⟨fun offset => (everywhereBoth offset).1, fun offset => (everywhereBoth offset).2⟩
  · intro bothEverywhere
    exact fun offset => ⟨bothEverywhere.1 offset, bothEverywhere.2 offset⟩

/-- ★ `F` distributes over `∨`: `F(φ ∨ ψ) ↔ Fφ ∨ Fψ`. -/
theorem eventually_distrib_or {State : Type} (firstProp secondProp : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    eventually (orOp firstProp secondProp) stream time
      ↔ orOp (eventually firstProp) (eventually secondProp) stream time := by
  constructor
  · intro someEither
    obtain ⟨offset, eitherAtOffset⟩ := someEither
    cases eitherAtOffset with
    | inl firstAtOffset => exact Or.inl ⟨offset, firstAtOffset⟩
    | inr secondAtOffset => exact Or.inr ⟨offset, secondAtOffset⟩
  · intro eitherSome
    cases eitherSome with
    | inl someFirst => obtain ⟨offset, atOffset⟩ := someFirst; exact ⟨offset, Or.inl atOffset⟩
    | inr someSecond => obtain ⟨offset, atOffset⟩ := someSecond; exact ⟨offset, Or.inr atOffset⟩

/-- ★ `X` distributes over `∧`: `X(φ ∧ ψ) ↔ Xφ ∧ Xψ` (`X` commutes with the connectives — by `Iff.rfl`). -/
theorem next_distrib_and {State : Type} (firstProp secondProp : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    next (andOp firstProp secondProp) stream time
      ↔ andOp (next firstProp) (next secondProp) stream time := Iff.rfl

/-- `Gφ → φ` — globally entails the present (`G` is reflexive). -/
theorem globally_implies_now {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    globally inner stream time → inner stream time :=
  fun everywhere => everywhere 0

/-- `φ → Fφ` — the present entails eventually. -/
theorem now_implies_eventually {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    inner stream time → eventually inner stream time :=
  fun atNow => ⟨0, atNow⟩

/-- `Gφ → Fφ` — globally entails eventually. -/
theorem globally_implies_eventually {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    globally inner stream time → eventually inner stream time :=
  fun everywhere => ⟨0, everywhere 0⟩

/-- ★ `φ U ψ → Fψ` — untilOp entails that the target eventually holds. -/
theorem untilOp_implies_eventually {State : Type} (waiting target : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    untilOp waiting target stream time → eventually target stream time :=
  fun untilOpHolds =>
    match untilOpHolds with
    | ⟨delay, targetAtDelay, _⟩ => ⟨delay, targetAtDelay⟩

/-- ★ `F¬φ → ¬Gφ` — the INTUITIONISTIC half of the `G`/`F` duality (the classical converse is a marker). -/
theorem eventually_not_implies_not_globally {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    eventually (notOp inner) stream time → ¬ globally inner stream time :=
  fun eventuallyNot everywhere =>
    match eventuallyNot with
    | ⟨offset, notAtOffset⟩ => notAtOffset (everywhere offset)

/-- `GGφ ↔ Gφ` — `G` is idempotent. -/
theorem globally_idempotent {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    globally (globally inner) stream time ↔ globally inner stream time := by
  constructor
  · intro nestedEverywhere
    intro offset
    exact nestedEverywhere offset 0
  · intro everywhere
    intro firstOffset secondOffset
    rw [Nat.add_assoc]
    exact everywhere (firstOffset + secondOffset)

/-! ## Honesty markers -/

/-- **Honesty marker.**  The CLASSICAL `G`/`F` duality converse `¬Gφ → F¬φ` (and `¬Fφ → G¬φ`) — needs
`¬∀ → ∃¬`, i.e. `Classical.choice` — is deferred (the intuitionistic half IS shipped).  `= false`. -/
def fxMode_hasClassicalTemporalDuality : Bool := false

/-- **Honesty marker.**  The coinductive FIXPOINT characterizations `Fφ ↔ φ ∨ XFφ`, `Gφ ↔ φ ∧ XGφ`,
`φUψ ↔ ψ ∨ (φ ∧ X(φUψ))` (the μ/ν presentation) are deferred.  `= false`. -/
def fxMode_hasTemporalFixpointLaws : Bool := false

/-- **Honesty marker.**  CTL branching time — the path quantifiers `A` / `E` over computation TREES (here a single
linear stream) — is deferred.  `= false`. -/
def fxMode_hasBranchingTime : Bool := false

/-- **Honesty marker.**  The LTL decision procedure (Büchi automata / bounded model checking decidability over
finite-state streams) is deferred.  `= false`. -/
def fxMode_hasLtlDecisionProcedure : Bool := false

/-- **Honesty marker.**  The kernel hardware temporal operators (§13.18) desugared into the kernel codata streams
(cross-axis, `fib`) is deferred.  `= false`. -/
def fxMode_hasKernelTemporalFibration : Bool := false

end FX1Poly.Tier0
