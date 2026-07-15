import FX1Poly.Axis.Mode.Mode

/-! # mode-15 — guarded / clock MTT: the clock mode (later, Löb, clock-irrelevance, unique fixpoints)

Guarded type theory (the topos of trees; Clocked/Ticked TT — Bizjak–Møgelberg et al.) adds the **later**
modality `▷` (a value available "one step later"), an applicative `next`/`⊛`, and **Löb induction** — the
guarded fixed point `löb : (▷A → A) → A` with the computation rule `löb f = f (next (löb f))`.  **Clocks** index
the time steps, and **clock irrelevance** (`∀κ. A ≅ A` for clock-independent `A`) is what turns guarded
recursion into genuine coinduction.  Guarded fixed points are **unique**.

`mode-15` ships the later/Löb interface with its computation rule, a concrete witness, the UNIQUE-fixpoint
theorem, and clock irrelevance for the single-clock model.

## What this file ships (each piece zero-axiom)

  * **`LaterModality`** — `Later` (`▷`) + `next` + `ap` (`⊛`) + `lob`, with the applicative law `ap_next` and
    the **Löb computation rule** `lob_unfold` (`löb f = f (next (löb f))`) as structure fields.
  * **`trivialLater`** — the concrete witness (`▷A = Unit`), with `ap_next` and the Löb rule by `rfl`.  This is
    the only zero-axiom model AT THE `Type → Type` signature (a total `löb` there must collapse).
  * ★ **`stepIndexedLob`** — the GENUINE non-trivial Löb at the step-indexed `Nat → Type` signature (the topos of
    trees): `laterShift` actually shifts (`▷X 0 = PUnit`, `▷X (n+1) = X n`) and `lob` is total by structural
    recursion, with `constStream_depth_two` witnessing a non-degenerate fixpoint.  This corrects the reading of
    `trivialLater` as "the only zero-axiom later."
  * **`trivialLater_lob_isUnique`** — the UNIQUE-fixpoint property: every fixed point of a guarded step IS
    `löb`.  PROVED.
  * the single-clock model: **`ClockQuantified`** (`∀κ.A = Unit → A`) + **`forceClock`** / **`constantClock`**
    with **`clockIrrelevance`** (`∀κ.A ≅ A` by eta — both round trips).

## What is DEFERRED (markers)

  * the FULL presheaf topos-of-trees later — `stepIndexedLob` ships the raw step-indexed `▷` / `lob` (genuine
    shift + non-trivial fixpoint); what remains deferred is the restriction-map functoriality + naturality of the
    genuine presheaf model (`hasToposOfTreesLater`);
  * the MULTI-CLOCK model + clock quantification giving coinductive-from-guarded — the single Unit-clock is
    degenerate (`hasMultiClockModel`);
  * guarded COINDUCTION (forcing coinductive types out of guarded recursive ones) (`hasGuardedCoinduction`);
  * a kernel `later` / `löb` former (cross-axis; none exists in the `Generator` table — the temporal `gen_nextT`
    etc. are LTL, a different modality) (`hasKernelLaterFormer`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis

/-! ## The later modality + Löb -/

/-- A **later modality** — `Later` (`▷`) with its applicative `next` / `ap` and the guarded fixed point `lob`,
subject to the applicative law and the **Löb computation rule**. -/
structure LaterModality where
  /-- The later modality `▷`. -/
  Later : Type → Type
  /-- The unit `next : A → ▷A`. -/
  next : {A : Type} → A → Later A
  /-- The applicative `⊛ : ▷(A → B) → ▷A → ▷B`. -/
  ap : {A B : Type} → Later (A → B) → Later A → Later B
  /-- Löb induction: the guarded fixed point. -/
  lob : {A : Type} → (Later A → A) → A
  /-- The applicative homomorphism law: `next f ⊛ next a = next (f a)`. -/
  ap_next : {A B : Type} → (function : A → B) → (argument : A) →
    ap (next function) (next argument) = next (function argument)
  /-- The **Löb computation rule**: `löb f = f (next (löb f))`. -/
  lob_unfold : {A : Type} → (guardedStep : Later A → A) →
    lob guardedStep = guardedStep (next (lob guardedStep))

/-- The **trivial later** (`▷A = Unit`) — the concrete witness.  The applicative law and the Löb rule hold by
`rfl` (everything in `▷A = Unit` is the point).  Degenerate, and the only zero-axiom model AT THIS
`Later : Type → Type` signature (a total `lob` here must collapse); the GENUINE non-trivial Löb lives at the
step-indexed `Nat → Type` signature — see `stepIndexedLob` below. -/
def trivialLater : LaterModality where
  Later := fun _carrier => Unit
  next := fun _value => ()
  ap := fun _laterFunction _laterArgument => ()
  lob := fun guardedStep => guardedStep ()
  ap_next := fun _function _argument => rfl
  lob_unfold := fun _guardedStep => rfl

/-- Smoke: a constant guarded step's Löb fixed point is the constant. -/
theorem trivialLater_lob_const {A : Type} (value : A) :
    trivialLater.lob (fun _later => value) = value := rfl

/-- ★ **Guarded fixed points are UNIQUE** (for the trivial later): every fixed point of a guarded step equals
its `löb`.  Because `next` collapses everything to the point, `f (next x) = f (next (löb f))`. -/
theorem trivialLater_lob_isUnique {A : Type} (guardedStep : trivialLater.Later A → A) (fixedPoint : A)
    (isFixed : fixedPoint = guardedStep (trivialLater.next fixedPoint)) :
    fixedPoint = trivialLater.lob guardedStep :=
  isFixed.trans rfl

/-! ## Clocks + clock irrelevance -/

/-- **Clock quantification** in the single-clock model — `∀κ. A` modeled as `Unit → A`. -/
abbrev ClockQuantified (A : Type) : Type := Unit → A

/-- **Force** — evaluate a clock-quantified value at the clock (the clock-irrelevance projection). -/
def forceClock {A : Type} (clockedValue : ClockQuantified A) : A := clockedValue ()

/-- The constant clock-quantified value. -/
def constantClock {A : Type} (value : A) : ClockQuantified A := fun _clock => value

/-- Force after constant is the identity (`force (Λκ. a) = a`). -/
theorem forceClock_constantClock {A : Type} (value : A) :
    forceClock (constantClock value) = value := rfl

/-- ★ **Clock irrelevance** (single-clock model): `∀κ. A ≃ A` for clock-independent `A` — constant after force
is the identity, so with `forceClock_constantClock` the two are inverse.  By eta (function + `Unit`), no funext. -/
theorem clockIrrelevance {A : Type} (clockedValue : ClockQuantified A) :
    constantClock (forceClock clockedValue) = clockedValue := rfl

/-! ## The genuine step-indexed later — a NON-TRIVIAL Löb (the topos-of-trees model)

`trivialLater` is the only zero-axiom model AT THE `Later : Type → Type` SIGNATURE (a total `lob` there must
collapse — `lob f = f (lob f)` would loop).  The GENUINE later lives at the step-indexed signature
`StepIndexedType := Nat → Type` (the topos of trees): `▷` SHIFTS the approximation one step, and `lob` is total
by STRUCTURAL RECURSION on the step index — a genuinely non-trivial fixpoint.  This section ships that model,
correcting any reading of `trivialLater` as "the only zero-axiom later." -/

/-- A **step-indexed type** — an object of the topos of trees as a raw `Nat`-indexed family of approximations
(the depth-`n` view at index `n`). -/
def StepIndexedType : Type 1 := Nat → Type

/-- The **later shift** `▷` on step-indexed types: `(▷X) 0 = PUnit`, `(▷X)(n+1) = X n` — genuinely shifting the
approximation one step (unlike `trivialLater`'s constant `Unit`). -/
def laterShift (stepType : StepIndexedType) : Nat → Type
  | 0 => PUnit
  | nextStep + 1 => stepType nextStep

/-- ★ The **genuine guarded fixpoint** (Löb): from a generator `▷X → X` presented as the level-indexed family
`(n) → (▷X) n → X n`, build `(n) → X n` by STRUCTURAL RECURSION on the step index.  At step 0 the generator
consumes the trivial `▷X` approximation; at step `n+1` it consumes the depth-`n` fixpoint.  Total and NON-TRIVIAL
— each `X (n+1)` is genuinely built from `X n`, with no `▷ = Unit` collapse. -/
def stepIndexedLob {stepType : StepIndexedType}
    (generator : (step : Nat) → laterShift stepType step → stepType step) :
    (step : Nat) → stepType step
  | 0 => generator 0 PUnit.unit
  | nextStep + 1 => generator (nextStep + 1) (stepIndexedLob generator nextStep)

/-- The Löb computation at step 0 — the fixpoint consumes the trivial approximation. -/
theorem stepIndexedLob_zero {stepType : StepIndexedType}
    (generator : (step : Nat) → laterShift stepType step → stepType step) :
    stepIndexedLob generator 0 = generator 0 PUnit.unit := rfl

/-- ★ The Löb computation at step `n+1`: `lob gen (n+1) = gen (n+1) (lob gen n)` — the genuine unfold building
the depth-`(n+1)` fixpoint from the depth-`n` one. -/
theorem stepIndexedLob_succ {stepType : StepIndexedType}
    (generator : (step : Nat) → laterShift stepType step → stepType step) (nextStep : Nat) :
    stepIndexedLob generator (nextStep + 1)
      = generator (nextStep + 1) (stepIndexedLob generator nextStep) := rfl

/-- The step-indexed type of **stream approximations**: `streamApprox A n` is the depth-`n` prefix `Aⁿ`
(`streamApprox A 0 = PUnit`, `streamApprox A (n+1) = A × streamApprox A n`). -/
def streamApprox (A : Type) : Nat → Type
  | 0 => PUnit
  | nextStep + 1 => A × streamApprox A nextStep

/-- The guarded generator for the CONSTANT stream — prepend the fixed value at each step. -/
def constStreamGenerator {A : Type} (constValue : A) :
    (step : Nat) → laterShift (streamApprox A) step → streamApprox A step
  | 0 => fun _ => PUnit.unit
  | _nextStep + 1 => fun tail => (constValue, tail)

/-- ★ **Non-degeneracy**: the constant stream's depth-2 approximation is genuinely `(a, (a, ()))` — the
step-indexed `lob` populates each finite stage, NOT collapsing to `Unit`.  The concrete proof that the genuine
zero-axiom Löb is non-trivial. -/
theorem constStream_depth_two {A : Type} (constValue : A) :
    stepIndexedLob (constStreamGenerator constValue) 2
      = (constValue, (constValue, PUnit.unit)) := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The raw step-indexed later (`▷` actually shifts, `löb` non-trivial via step-indexing
over `Nat`) IS now shipped — `laterShift` / `stepIndexedLob` / `constStream_depth_two` at the `Nat → Type`
signature.  What remains deferred is the FULL presheaf topos-of-trees: the restriction maps `X(n+1) → X(n)` +
the functoriality / naturality of `▷` and `next` as a presheaf endofunctor.  `= false`. -/
def fxMode_hasToposOfTreesLater : Bool := false

/-- **Honesty marker.**  The MULTI-CLOCK model + clock quantification (`∀κ`) yielding genuine coinductive types
from guarded ones is deferred — the single `Unit`-clock here is degenerate.  `= false`. -/
def fxMode_hasMultiClockModel : Bool := false

/-- **Honesty marker.**  Guarded COINDUCTION — forcing coinductive types out of guarded recursive types (the
headline application of clocks) — is deferred.  `= false`. -/
def fxMode_hasGuardedCoinduction : Bool := false

/-- **Honesty marker.**  A kernel `later` / `löb` former is deferred — none exists in the `Generator` table (the
temporal `gen_nextT` / `gen_alwaysT` etc. are LTL, a DIFFERENT modality); cross-axis (`fib`).  `= false`. -/
def fxMode_hasKernelLaterFormer : Bool := false

end FX1Poly.Axis
