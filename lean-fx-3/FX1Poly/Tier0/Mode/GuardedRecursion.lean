import FX1Poly.Tier0.Mode.Mode

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
    the ONLY zero-axiom model: a non-trivial `löb` needs the step-indexed shift (a general `löb f = f (löb f)`
    on `▷ = Id` would not terminate).
  * **`trivialLater_lob_isUnique`** — the UNIQUE-fixpoint property: every fixed point of a guarded step IS
    `löb`.  PROVED.
  * the single-clock model: **`ClockQuantified`** (`∀κ.A = Unit → A`) + **`forceClock`** / **`constantClock`**
    with **`clockIrrelevance`** (`∀κ.A ≅ A` by eta — both round trips).

## What is DEFERRED (markers)

  * the genuine TOPOS-OF-TREES later (where `▷` actually shifts, `löb` non-trivial via step-indexing) — the
    trivial `▷ = Unit` is degenerate (`hasToposOfTreesLater`);
  * the MULTI-CLOCK model + clock quantification giving coinductive-from-guarded — the single Unit-clock is
    degenerate (`hasMultiClockModel`);
  * guarded COINDUCTION (forcing coinductive types out of guarded recursive ones) (`hasGuardedCoinduction`);
  * a kernel `later` / `löb` former (cross-axis; none exists in the `Generator` table — the temporal `gen_nextT`
    etc. are LTL, a different modality) (`hasKernelLaterFormer`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

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
`rfl` (everything in `▷A = Unit` is the point).  Degenerate, but the only zero-axiom model. -/
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

/-! ## Honesty markers -/

/-- **Honesty marker.**  The genuine TOPOS-OF-TREES later (`▷` actually shifts, `löb` non-trivial via
step-indexing over `Nat`) is deferred — `trivialLater`'s `▷ = Unit` is degenerate.  `= false`. -/
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

end FX1Poly.Tier0
