/-! # StepRefinement: forward step-refinement against a golden ISA (fx_design.md §13.19 / §18.12)

The §13.19 `bisimulation` triple (`relates`/`initial`/`step`) over the §18.12
golden-reference framing, carrying `abstracts : ImplState → ArchState → Prop`.  The
`stepRefines` obligation, with `initial`, lifts the correspondence to every
reachable run (`iterate`/`onAllRuns`), transporting ISA-level properties along a
trace.

Generic: the identity instance inhabits the relation and the lifting is proved, but
no concrete pipeline `implStep` or non-identity simulation against a real ISA
appears — the per-target §18.12/§20.7 CompCert / CHERIoT-Ibex obligation, made
statable and checkable, not discharged.  `Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- Total `n`-fold self-iteration of a step function, structural on the count
(a local definition, not core `^[·]`, keeping the layer self-contained). -/
def iterateStep {State : Type} (step : State → State) : Nat → State → State
  | 0,          state => state
  | count + 1,  state => iterateStep step count (step state)

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
  /-- One implementation step preserves the relation. -/
  stepRefines : ∀ (impl : ImplState) (arch : ArchState),
                  abstracts impl arch →
                    abstracts (implStep impl) (archStep arch)

/-- Multi-step lifting by induction on the count (successor via `stepRefines`). -/
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

/-- Whole-trace correspondence: `initial` fed through the multi-step lifting. -/
theorem StepRefinement.onAllRuns {ImplState ArchState : Type}
    (refinement : StepRefinement ImplState ArchState) (count : Nat) :
    refinement.abstracts
      (iterateStep refinement.implStep count refinement.implInit)
      (iterateStep refinement.archStep count refinement.archInit) :=
  refinement.iterate count refinement.implInit refinement.archInit refinement.initial

/-! ## Functional special case (§18.12 `via fn`) -/

/-- Refinement from a functional abstraction with commuting square
`abstract (implStep i) = archStep (abstract i)` (the §18.12 `via fn` case). -/
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

/-! ## Identity refinement (inhabitation) -/

/-- Identity forward simulation (implementation equals golden reference, `Eq`),
inhabiting `StepRefinement`. -/
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

/-- Witness over `Nat`: `n ↦ n + 1` is its own golden reference. -/
def natSuccorRefinement : StepRefinement Nat Nat :=
  StepRefinement.identity (fun value => value + 1) 0

end FX1Poly.ComputerAlgebra
