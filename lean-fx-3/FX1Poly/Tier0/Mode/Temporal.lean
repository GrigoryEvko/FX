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

/-! ## The μ/ν fixpoint unfolding laws (discharges hasTemporalFixpointLaws) -/

/-- Offset bookkeeping: `time + 1 + step = time + (step + 1)` (the one-step shift the fixpoint laws thread). -/
theorem temporalAddShift (timeIndex stepCount : Nat) :
    timeIndex + 1 + stepCount = timeIndex + (stepCount + 1) :=
  Nat.succ_add timeIndex stepCount

/-- ★ `Fφ ↔ φ ∨ XFφ` — the μ-fixpoint unfolding of eventually. -/
theorem eventually_fixpoint {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    eventually inner stream time ↔ orOp inner (next (eventually inner)) stream time := by
  constructor
  · intro someFuture
    obtain ⟨offset, atOffset⟩ := someFuture
    cases offset with
    | zero => exact Or.inl atOffset
    | succ earlier =>
        refine Or.inr ⟨earlier, ?_⟩
        rw [temporalAddShift]
        exact atOffset
  · intro nowOrLater
    cases nowOrLater with
    | inl atNow => exact ⟨0, atNow⟩
    | inr laterStep =>
        obtain ⟨offset, atOffset⟩ := laterStep
        refine ⟨offset + 1, ?_⟩
        rw [← temporalAddShift]
        exact atOffset

/-- ★ `Gφ ↔ φ ∧ XGφ` — the ν-fixpoint unfolding of globally. -/
theorem globally_fixpoint {State : Type} (inner : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    globally inner stream time ↔ andOp inner (next (globally inner)) stream time := by
  constructor
  · intro everywhere
    refine ⟨everywhere 0, fun offset => ?_⟩
    rw [temporalAddShift]
    exact everywhere (offset + 1)
  · intro nowAndLater
    intro offset
    cases offset with
    | zero => exact nowAndLater.1
    | succ earlier =>
        have laterHolds := nowAndLater.2 earlier
        rw [temporalAddShift] at laterHolds
        exact laterHolds

/-- ★ `φUψ ↔ ψ ∨ (φ ∧ X(φUψ))` — the μ-fixpoint unfolding of until. -/
theorem untilOp_fixpoint {State : Type} (waiting target : TemporalProp State)
    (stream : CycleStream State) (time : Nat) :
    untilOp waiting target stream time
      ↔ orOp target (andOp waiting (next (untilOp waiting target))) stream time := by
  constructor
  · intro untilHolds
    obtain ⟨delay, targetAtDelay, waitBefore⟩ := untilHolds
    cases delay with
    | zero => exact Or.inl targetAtDelay
    | succ priorDelay =>
        refine Or.inr ⟨waitBefore 0 (Nat.succ_pos priorDelay), priorDelay, ?_, fun earlier isBefore => ?_⟩
        · rw [temporalAddShift]; exact targetAtDelay
        · rw [temporalAddShift]; exact waitBefore (earlier + 1) (Nat.succ_lt_succ isBefore)
  · intro targetOrStep
    cases targetOrStep with
    | inl targetNow => exact ⟨0, targetNow, fun earlier isBefore => absurd isBefore (Nat.not_lt_zero earlier)⟩
    | inr waitAndStep =>
        obtain ⟨waitNow, delay, targetAtDelay, waitBefore⟩ := waitAndStep
        refine ⟨delay + 1, ?_, fun earlier isBefore => ?_⟩
        · rw [← temporalAddShift]; exact targetAtDelay
        · cases earlier with
          | zero => exact waitNow
          | succ priorEarlier =>
              rw [← temporalAddShift]
              exact waitBefore priorEarlier (Nat.lt_of_succ_lt_succ isBefore)

/-! ## CTL branching time over a transition relation (discharges hasBranchingTime) -/

/-- Reachability — the reflexive-transitive closure of a transition relation (a path of any length). -/
inductive ReachableVia {State : Type} (transition : State → State → Prop) : State → State → Prop
  /-- The empty path. -/
  | refl (state : State) : ReachableVia transition state state
  /-- One transition, then a reachable tail. -/
  | step {source middle target : State} (edge : transition source middle)
      (rest : ReachableVia transition middle target) : ReachableVia transition source target

/-- Path concatenation — reachability is transitive. -/
theorem ReachableVia.append {State : Type} {transition : State → State → Prop} {source middle target : State}
    (first : ReachableVia transition source middle) :
    ReachableVia transition middle target → ReachableVia transition source target := by
  induction first with
  | refl => exact id
  | step edge _ ih => exact fun second => .step edge (ih second)

/-- `EX φ` — SOME successor satisfies `φ`. -/
def ctlEX {State : Type} (transition : State → State → Prop) (inner : State → Prop) (state : State) : Prop :=
  ∃ successor, transition state successor ∧ inner successor

/-- `AX φ` — ALL successors satisfy `φ`. -/
def ctlAX {State : Type} (transition : State → State → Prop) (inner : State → Prop) (state : State) : Prop :=
  ∀ successor, transition state successor → inner successor

/-- `EF φ` — `φ` holds at SOME reachable state. -/
def ctlEF {State : Type} (transition : State → State → Prop) (inner : State → Prop) (state : State) : Prop :=
  ∃ reached, ReachableVia transition state reached ∧ inner reached

/-- `AG φ` — `φ` holds at EVERY reachable state. -/
def ctlAG {State : Type} (transition : State → State → Prop) (inner : State → Prop) (state : State) : Prop :=
  ∀ reached, ReachableVia transition state reached → inner reached

/-- `AGφ → φ` — globally entails the present (the current state is reachable from itself). -/
theorem ctlAG_implies_here {State : Type} (transition : State → State → Prop) (inner : State → Prop)
    (state : State) : ctlAG transition inner state → inner state :=
  fun everywhere => everywhere state (ReachableVia.refl state)

/-- `φ → EFφ` — the present entails reachability. -/
theorem ctlHere_implies_EF {State : Type} (transition : State → State → Prop) (inner : State → Prop)
    (state : State) : inner state → ctlEF transition inner state :=
  fun atHere => ⟨state, ReachableVia.refl state, atHere⟩

/-- ★ `AGφ → AX(AGφ)` — the CTL ν-fixpoint unfolding (`AG` invariance pushes through every successor). -/
theorem ctlAG_unfold {State : Type} (transition : State → State → Prop) (inner : State → Prop)
    (state : State) : ctlAG transition inner state → ctlAX transition (ctlAG transition inner) state := by
  intro everywhere successor edge reached reachFromSuccessor
  exact everywhere reached (ReachableVia.step edge reachFromSuccessor)

/-- `AG` distributes over `∧`. -/
theorem ctlAG_and_distrib {State : Type} (transition : State → State → Prop) (firstProp secondProp : State → Prop)
    (state : State) :
    ctlAG transition (fun reached => firstProp reached ∧ secondProp reached) state
      ↔ ctlAG transition firstProp state ∧ ctlAG transition secondProp state := by
  constructor
  · intro everywhereBoth
    exact ⟨fun reached path => (everywhereBoth reached path).1,
           fun reached path => (everywhereBoth reached path).2⟩
  · intro bothEverywhere
    exact fun reached path => ⟨bothEverywhere.1 reached path, bothEverywhere.2 reached path⟩

/-- `EF` distributes over `∨`. -/
theorem ctlEF_or_distrib {State : Type} (transition : State → State → Prop) (firstProp secondProp : State → Prop)
    (state : State) :
    ctlEF transition (fun reached => firstProp reached ∨ secondProp reached) state
      ↔ ctlEF transition firstProp state ∨ ctlEF transition secondProp state := by
  constructor
  · intro someEither
    obtain ⟨reached, path, eitherHere⟩ := someEither
    cases eitherHere with
    | inl firstHere => exact Or.inl ⟨reached, path, firstHere⟩
    | inr secondHere => exact Or.inr ⟨reached, path, secondHere⟩
  · intro eitherSome
    cases eitherSome with
    | inl someFirst => obtain ⟨reached, path, here⟩ := someFirst; exact ⟨reached, path, Or.inl here⟩
    | inr someSecond => obtain ⟨reached, path, here⟩ := someSecond; exact ⟨reached, path, Or.inr here⟩

/-! ### The branching witness: `EX ≠ AX` (a single linear stream cannot express this) -/

/-- A genuinely BRANCHING transition: from `true` every state is a successor; from `false` only `false`. -/
def branchingTransition (source target : Bool) : Prop := source = true ∨ target = false

/-- ★ At `true` SOME successor is `true` — `EX (·=true)` holds. -/
theorem branching_EX_holds : ctlEX branchingTransition (fun state => state = true) true :=
  ⟨true, Or.inl rfl, rfl⟩

/-- ★ At `true` NOT all successors are `true` (`false` is reachable in one step) — `AX (·=true)` FAILS.  Together
with `branching_EX_holds` this proves `EX` and `AX` genuinely differ — the defining branching-time fact a single
linear stream cannot witness. -/
theorem branching_AX_fails : ¬ ctlAX branchingTransition (fun state => state = true) true := by
  intro allSuccessors
  exact Bool.noConfusion (allSuccessors false (Or.inl rfl))

/-! ## Honesty markers -/

/-- **Honesty marker.**  The CLASSICAL `G`/`F` duality converse `¬Gφ → F¬φ` (and `¬Fφ → G¬φ`) — needs
`¬∀ → ∃¬`, i.e. `Classical.choice` — is deferred (the intuitionistic half IS shipped).  `= false`. -/
def fxMode_hasClassicalTemporalDuality : Bool := false

/-- The μ/ν FIXPOINT characterizations are SHIPPED intuitionistically: `Fφ ↔ φ ∨ XFφ` (`eventually_fixpoint`),
`Gφ ↔ φ ∧ XGφ` (`globally_fixpoint`), `φUψ ↔ ψ ∨ (φ ∧ X(φUψ))` (`untilOp_fixpoint`).  `= true`. -/
def fxMode_hasTemporalFixpointLaws : Bool := true

/-- CTL branching time is SHIPPED over a transition relation: the path quantifiers `ctlEX`/`ctlAX`/`ctlEF`/`ctlAG`,
the `AGφ → AX(AGφ)` unfold, AG/EF distribution, and the ★ branching witness `branching_EX_holds` +
`branching_AX_fails` proving `EX ≠ AX` (impossible on a single linear stream).  `= true`. -/
def fxMode_hasBranchingTime : Bool := true

/-- **Honesty marker.**  The LTL decision procedure (Büchi automata / ω-automata emptiness) is deferred — the
reachability fragment `ctlEF`/`ctlAG` IS decidable on finite models, but the full Büchi construction is not shipped.
`= false`. -/
def fxMode_hasLtlDecisionProcedure : Bool := false

/-- **Honesty marker.**  The kernel hardware temporal operators (§13.18) desugared into the kernel codata streams
(cross-axis, `fib`) is deferred.  `= false`. -/
def fxMode_hasKernelTemporalFibration : Bool := false

end FX1Poly.Tier0
