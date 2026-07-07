/-! # StepRefinement — the forward step-refinement scaffold (fx_design.md §13.19 / §18.12)

The first mechanization (scaffold half) of the FX refinement dimension: a two-carrier
state relation `abstracts : ImplState -> ArchState -> Prop` together with the §13.19
`bisimulation`-block triple (`relates` / `initial` / `step`) and the §18.12
golden-reference framing (`archStep` = the `Tot` spec step, `implStep` = the
implementation step, `abstracts` = the `via` abstraction in relational form).

The load-bearing obligation is the `stepRefines` field — the step-refinement theorem
shape

  forall impl arch, abstracts impl arch -> abstracts (implStep impl) (archStep arch)

paired with `initial : abstracts implInit archInit`.  From these two the scaffold
lifts the correspondence to EVERY reachable run (`iterate` / `onAllRuns`), so any
ISA-level property transports along a whole trace.

This file is the SCAFFOLD ONLY.  It is generic, non-vacuous (the identity instance
below inhabits it), and proves the multi-step lifting.  It deliberately does NOT
contain any concrete pipeline `implStep` nor a non-identity forward simulation of a
real pipeline against a real ISA — that is the per-target, effectively-unbounded
content of §18.12/§20.7 (the CompCert / CHERIoT-Ibex-style obligation).  The scaffold
makes those instances statable and checkable; it does not make any of them true.

`Init`-only, structural, zero axioms — every proof is `rfl` / `congrArg` / one
structural `Nat` recursion. -/

namespace FX1Poly.ComputerAlgebra

/-- Total `n`-fold self-iteration of a step function, structural on the count.
`iterateStep step (n+1) state = iterateStep step n (step state)` — apply once, then
iterate the rest.  Own definition (no core `^[_]`) keeps the layer self-contained and
manifestly zero-axiom. -/
def iterateStep {State : Type} (step : State → State) : Nat → State → State
  | 0,          state => state
  | count + 1,  state => iterateStep step count (step state)

/-- A forward (step) refinement of an implementation against a golden ISA reference.

* `archStep`    — golden reference one-step (§18.12 `spec = step`),
* `implStep`    — implementation one-step (§18.12 `impl`),
* `abstracts`   — the relation `R : ImplState -> ArchState -> Prop` (§13.19 `relates`,
  the §18.12 `via` abstraction in relational form),
* `initial`     — §13.19 `initial`: the initial states are related,
* `stepRefines` — §13.19 `step`: one implementation step preserves the relation. -/
structure StepRefinement (ImplState ArchState : Type) where
  /-- Golden-reference one-step function. -/
  archStep    : ArchState → ArchState
  /-- Implementation one-step function. -/
  implStep    : ImplState → ImplState
  /-- The abstraction relation `R`. -/
  abstracts   : ImplState → ArchState → Prop
  /-- The implementation's initial state. -/
  implInit    : ImplState
  /-- The golden reference's initial state. -/
  archInit    : ArchState
  /-- The initial states are related. -/
  initial     : abstracts implInit archInit
  /-- One implementation step preserves the relation against one golden step. -/
  stepRefines : ∀ (impl : ImplState) (arch : ArchState),
                  abstracts impl arch →
                    abstracts (implStep impl) (archStep arch)

/-- The multi-step lifting: `n` implementation steps stay related to `n` golden steps.
Structural induction on the step count, discharging the successor case by the IH on the
once-advanced pair (`stepRefines`). -/
theorem StepRefinement.iterate {ImplState ArchState : Type}
    (refinement : StepRefinement ImplState ArchState) :
    ∀ (count : Nat) (impl : ImplState) (arch : ArchState),
      refinement.abstracts impl arch →
        refinement.abstracts
          (iterateStep refinement.implStep count impl)
          (iterateStep refinement.archStep count arch)
  | 0,          _,    _,    related => related
  | count + 1,  impl, arch, related =>
      refinement.iterate count (refinement.implStep impl) (refinement.archStep arch)
        (refinement.stepRefines impl arch related)

/-- Every reachable implementation run abstracts to the corresponding golden run: the
whole-trace correspondence, obtained by feeding `initial` through the multi-step lift. -/
theorem StepRefinement.onAllRuns {ImplState ArchState : Type}
    (refinement : StepRefinement ImplState ArchState) (count : Nat) :
    refinement.abstracts
      (iterateStep refinement.implStep count refinement.implInit)
      (iterateStep refinement.archStep count refinement.archInit) :=
  refinement.iterate count refinement.implInit refinement.archInit refinement.initial

/-! ## The functional special case (§18.12 `via fn` — the commuting square) -/

/-- Build a refinement from a functional abstraction `abstract : ImplState -> ArchState`
whose commuting square `abstract (implStep i) = archStep (abstract i)` holds.  The
relation is `R i a := abstract i = a`; `initial` is `rfl`; `stepRefines` chains the
square with `congrArg`.  This is the §18.12 `abstract(tick(p)) == step(abstract(...))`
correspondence in constructive form. -/
def StepRefinement.ofAbstraction {ImplState ArchState : Type}
    (archStep : ArchState → ArchState) (implStep : ImplState → ImplState)
    (abstract : ImplState → ArchState) (implInit : ImplState)
    (square : ∀ impl, abstract (implStep impl) = archStep (abstract impl)) :
    StepRefinement ImplState ArchState :=
  { archStep    := archStep
  , implStep    := implStep
  , abstracts   := fun impl arch => abstract impl = arch
  , implInit    := implInit
  , archInit    := abstract implInit
  , initial     := rfl
  , stepRefines := fun impl _ related => (square impl).trans (congrArg archStep related) }

/-! ## The identity refinement — the scaffold is inhabited (non-vacuous) -/

/-- The identity forward simulation: the implementation IS the golden reference,
related by `Eq`.  All obligations discharge by `rfl` / `congrArg` — proving the
`StepRefinement` type is inhabited and non-vacuous over ANY golden step. -/
def StepRefinement.identity {ArchState : Type}
    (archStep : ArchState → ArchState) (archInit : ArchState) :
    StepRefinement ArchState ArchState :=
  { archStep    := archStep
  , implStep    := archStep
  , abstracts   := Eq
  , implInit    := archInit
  , archInit    := archInit
  , initial     := rfl
  , stepRefines := fun _ _ related => congrArg archStep related }

/-- Concrete smoke witness over `Nat`: `n |-> n + 1` is its own golden reference. -/
def natSuccorRefinement : StepRefinement Nat Nat :=
  StepRefinement.identity (fun value => value + 1) 0

end FX1Poly.ComputerAlgebra
