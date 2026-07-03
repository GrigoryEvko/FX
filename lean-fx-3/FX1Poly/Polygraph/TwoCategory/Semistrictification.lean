import FX1Poly.Polygraph.TwoCategory.GlobularSet

/-! # mode-7 — Simpson semistrictification + the Eckmann–Hilton obstruction

`mode-5` gave the GRAY semistrictification (strict associativity + strict units, WEAK interchange — the
interchanger 3-cell).  `mode-6` gave the fully WEAK ω-category (everything weak, coherence by the contraction).
`mode-7` is the COMPLEMENTARY semistrictification, **Simpson's**: associativity AND interchange strict, only the
UNITS weak.  Simpson's conjecture (Carlos Simpson, "Homotopy types of strict 3-groupoids", 1998) is that every
weak ω-category is equivalent to such a SEMISTRICT one — strict except for weak units.

## Why the units are the ONE thing that cannot be strictified — the Eckmann–Hilton obstruction

The mathematical heart, and what this file actually PROVES (zero-axiom): the **Eckmann–Hilton argument**.  Two
binary operations on a carrier that share a common two-sided unit and satisfy the middle-four INTERCHANGE law
are forced to (i) coincide, (ii) be commutative, (iii) be associative — i.e. they collapse to a single
commutative monoid.  In a higher category the vertical and horizontal compositions of the endo-2-cells of an
identity share the identity 2-cell as unit and satisfy interchange; iterated to dimension ≥ 3 (for groupoids)
this forced over-commutativity is exactly the Brown–Higgins / Simpson obstruction — strict ω-groupoids cannot
model all homotopy types (e.g. the Whitehead product in `π₃(S²)`).  So semistrictification must keep the units
WEAK: that is the only degree of freedom Eckmann–Hilton leaves.

## What this file ships (each piece zero-axiom)

  * **`EckmannHilton`** — the obstruction data: a carrier, two operations `op1` / `op2`, a shared two-sided
    `unit`, and the middle-four `interchange` law.  Plus the FULL theorem:
    `op1_eq_op2` (the operations coincide), `medial` (the resulting four-way exchange), `op2_comm` /
    `op1_comm` (commutativity), `op2_assoc` (associativity).  All by `rw` on the unit + interchange equations
    (propext-clean — no `simp`).  Witnesses: `trivialEckmannHilton` (on `Unit`) and the genuine 2-element
    `boolAndEckmannHilton` (`Bool` under `&&`).
  * **`SemistrictOmegaCategory`** — the semistrict signature over a `mode-6` globular set: a composition with
    STRICT associativity (`compose_assoc`, an on-the-nose equation) and units provided WEAKLY by a
    `GlobularContraction` (a filler cell, not a unit equation) — the "strict except units" shape.
    `terminalSemistrictOmegaCategory` witnesses inhabitation.

## What is DEFERRED (recorded by `= false` markers)

  * Simpson's conjecture proper — every weak ω-category (`mode-6`) is biequivalent to a `SemistrictOmegaCategory`
    (`hasSimpsonSemistrictification`); the explicit semistrictification functor + the biequivalence
    (`hasSemistrictificationFunctor`); the formal strict-ω-groupoid homotopy obstruction beyond the elementary
    Eckmann–Hilton collapse (`hasStrictGroupoidHomotopyObstruction`).

Note (scope): `SemistrictOmegaCategory` is built on `RawGlobularSet`, the MODE-axis globular shape — NOT the
kernel's general cell substrate (see `fxMode_hasGeneralDirectedComplexCellShape` in `GlobularSet.lean`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Polygraph

/-! ## The Eckmann–Hilton obstruction -/

/-- The **Eckmann–Hilton data**: a carrier with two binary operations sharing a common two-sided `unit` and
satisfying the middle-four INTERCHANGE law `op1 (op2 a b) (op2 c d) = op2 (op1 a c) (op1 b d)`.  This is the
exact situation of the two compositions (vertical / horizontal) at the endo-2-cells of an identity — the seed
of the obstruction that forces the units of a semistrict ω-category to stay weak. -/
structure EckmannHilton where
  /-- The underlying carrier. -/
  Carrier : Type
  /-- The first binary operation (e.g. vertical composition). -/
  op1 : Carrier → Carrier → Carrier
  /-- The second binary operation (e.g. horizontal composition). -/
  op2 : Carrier → Carrier → Carrier
  /-- The shared two-sided unit. -/
  unit : Carrier
  /-- `unit` is a left unit for `op1`. -/
  op1_unit_left  : ∀ element, op1 unit element = element
  /-- `unit` is a right unit for `op1`. -/
  op1_unit_right : ∀ element, op1 element unit = element
  /-- `unit` is a left unit for `op2`. -/
  op2_unit_left  : ∀ element, op2 unit element = element
  /-- `unit` is a right unit for `op2`. -/
  op2_unit_right : ∀ element, op2 element unit = element
  /-- The middle-four interchange law relating the two operations. -/
  interchange : ∀ topLeft topRight bottomLeft bottomRight,
    op1 (op2 topLeft topRight) (op2 bottomLeft bottomRight)
      = op2 (op1 topLeft bottomLeft) (op1 topRight bottomRight)

/-- ★ **The two operations coincide.**  Padding each factor with the shared unit and applying interchange
collapses `op1` to `op2`.  (Eckmann–Hilton, step 1.) -/
theorem EckmannHilton.op1_eq_op2 (eckmannHilton : EckmannHilton)
    (leftFactor rightFactor : eckmannHilton.Carrier) :
    eckmannHilton.op1 leftFactor rightFactor = eckmannHilton.op2 leftFactor rightFactor := by
  have squareStep :=
    eckmannHilton.interchange leftFactor eckmannHilton.unit eckmannHilton.unit rightFactor
  rw [eckmannHilton.op2_unit_right, eckmannHilton.op2_unit_left,
      eckmannHilton.op1_unit_right, eckmannHilton.op1_unit_left] at squareStep
  exact squareStep

/-- ★ **The medial (four-way exchange) law.**  With `op1 = op2` the interchange law becomes the self-exchange
`m (m a b) (m c d) = m (m a c) (m b d)` of the single operation `op2` — the algebraic engine for the
commutativity and associativity below. -/
theorem EckmannHilton.medial (eckmannHilton : EckmannHilton)
    (topLeft topRight bottomLeft bottomRight : eckmannHilton.Carrier) :
    eckmannHilton.op2 (eckmannHilton.op2 topLeft topRight) (eckmannHilton.op2 bottomLeft bottomRight)
      = eckmannHilton.op2 (eckmannHilton.op2 topLeft bottomLeft)
          (eckmannHilton.op2 topRight bottomRight) := by
  rw [← eckmannHilton.op1_eq_op2 (eckmannHilton.op2 topLeft topRight)
        (eckmannHilton.op2 bottomLeft bottomRight),
      ← eckmannHilton.op1_eq_op2 topLeft bottomLeft,
      ← eckmannHilton.op1_eq_op2 topRight bottomRight]
  exact eckmannHilton.interchange topLeft topRight bottomLeft bottomRight

/-- ★ **`op2` is commutative.**  Padding with units and applying the medial law swaps the factors.
(Eckmann–Hilton, the commutativity conclusion.) -/
theorem EckmannHilton.op2_comm (eckmannHilton : EckmannHilton)
    (leftFactor rightFactor : eckmannHilton.Carrier) :
    eckmannHilton.op2 leftFactor rightFactor = eckmannHilton.op2 rightFactor leftFactor := by
  have squareStep :=
    eckmannHilton.medial eckmannHilton.unit leftFactor rightFactor eckmannHilton.unit
  rw [eckmannHilton.op2_unit_left, eckmannHilton.op2_unit_right,
      eckmannHilton.op2_unit_left, eckmannHilton.op2_unit_right] at squareStep
  exact squareStep

/-- ★ **`op2` is associative.**  Padding the middle slot with the unit and applying the medial law reassociates.
(Eckmann–Hilton, the associativity conclusion — needs only the medial law and the units.) -/
theorem EckmannHilton.op2_assoc (eckmannHilton : EckmannHilton)
    (first second third : eckmannHilton.Carrier) :
    eckmannHilton.op2 (eckmannHilton.op2 first second) third
      = eckmannHilton.op2 first (eckmannHilton.op2 second third) := by
  have squareStep := eckmannHilton.medial first second eckmannHilton.unit third
  rw [eckmannHilton.op2_unit_left, eckmannHilton.op2_unit_right] at squareStep
  exact squareStep

/-- `op1` inherits commutativity from `op2` through `op1_eq_op2`. -/
theorem EckmannHilton.op1_comm (eckmannHilton : EckmannHilton)
    (leftFactor rightFactor : eckmannHilton.Carrier) :
    eckmannHilton.op1 leftFactor rightFactor = eckmannHilton.op1 rightFactor leftFactor := by
  rw [eckmannHilton.op1_eq_op2 leftFactor rightFactor, eckmannHilton.op2_comm leftFactor rightFactor,
      ← eckmannHilton.op1_eq_op2 rightFactor leftFactor]

/-- The trivial Eckmann–Hilton datum on `Unit` — every law holds by `Unit` eta.  A witness that the hypotheses
are satisfiable (so the theorems above are not vacuous). -/
def trivialEckmannHilton : EckmannHilton where
  Carrier := Unit
  op1 := fun _ _ => ()
  op2 := fun _ _ => ()
  unit := ()
  op1_unit_left  := fun _ => rfl
  op1_unit_right := fun _ => rfl
  op2_unit_left  := fun _ => rfl
  op2_unit_right := fun _ => rfl
  interchange := fun _ _ _ _ => rfl

/-- ★ A GENUINE 2-element Eckmann–Hilton datum: `Bool` under `&&` (a commutative monoid with unit `true`).
Witnesses that the obstruction fires on a structure with more than one element — `op2_comm` / `op2_assoc`
specialize to the commutativity / associativity of `&&`. -/
def boolAndEckmannHilton : EckmannHilton where
  Carrier := Bool
  op1 := Bool.and
  op2 := Bool.and
  unit := true
  op1_unit_left  := fun _ => rfl
  op1_unit_right := fun element => by cases element <;> rfl
  op2_unit_left  := fun _ => rfl
  op2_unit_right := fun element => by cases element <;> rfl
  interchange := by
    intro topLeft topRight bottomLeft bottomRight
    cases topLeft <;> cases topRight <;> cases bottomLeft <;> cases bottomRight <;> rfl

/-! ## Semistrict ω-categories: strict associativity, WEAK units -/

/-- A **semistrict ω-category** (Simpson) over a `mode-6` globular set: a composition that is STRICTLY
ASSOCIATIVE (`compose_assoc`, an on-the-nose equation) with units provided WEAKLY by a `GlobularContraction`
(a filler cell witnessing the unit laws up to a higher cell, NOT a strict unit equation).  This is the "strict
except units" signature — the form Simpson's conjecture targets, and the form the Eckmann–Hilton obstruction
shows is the BEST possible (the units cannot also be strictified).  The full cross-dimensional strict
interchange is part of the deferred Simpson theory (see the markers). -/
structure SemistrictOmegaCategory where
  /-- The underlying globular set (the MODE-axis cell shape). -/
  underlying : RawGlobularSet
  /-- A composition on cells of each dimension. -/
  compose : {dim : Nat} → underlying.cells dim → underlying.cells dim → underlying.cells dim
  /-- STRICT associativity — an on-the-nose equation (the semistrict part that IS strict). -/
  compose_assoc : ∀ {dim : Nat} (first second third : underlying.cells dim),
    compose (compose first second) third = compose first (compose second third)
  /-- Units provided WEAKLY: a contraction fills every parallel pair, so the unit laws hold up to a higher
  cell rather than on the nose (the one part Eckmann–Hilton forbids strictifying). -/
  weakUnitor : GlobularContraction underlying

/-- The terminal globular set carries a (degenerate) semistrict structure — composition is the unique cell,
associativity holds by `Unit` eta, and the weak unitor is the terminal contraction.  A witness that
`SemistrictOmegaCategory` is inhabited. -/
def terminalSemistrictOmegaCategory : SemistrictOmegaCategory where
  underlying := terminalGlobularSet
  compose := fun _ _ => ()
  compose_assoc := fun _ _ _ => rfl
  weakUnitor := terminalGlobularContraction

/-! ## Honesty markers -/

/-- **Honesty marker.**  Simpson's conjecture proper — every WEAK ω-category (`mode-6`) is biequivalent to a
`SemistrictOmegaCategory` (strict associativity + strict interchange, weak units) — is deferred.  `= false`. -/
def fxMode_hasSimpsonSemistrictification : Bool := false

/-- **Honesty marker.**  The explicit semistrictification FUNCTOR (weak ω-category → semistrict) and the
biequivalence proof (the content of the conjecture) are deferred.  `= false`. -/
def fxMode_hasSemistrictificationFunctor : Bool := false

/-- **Honesty marker.**  The formal strict-ω-groupoid HOMOTOPY obstruction (Brown–Higgins / Simpson: strict
ω-groupoids fail to model all homotopy types — e.g. `π₃(S²)`), beyond the elementary Eckmann–Hilton collapse
shipped here, is deferred.  `= false`. -/
def fxMode_hasStrictGroupoidHomotopyObstruction : Bool := false

end FX1Poly.Polygraph
