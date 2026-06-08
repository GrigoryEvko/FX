import FX1Poly.Typed.TypedChurchNumeralComputeGeneral
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchSucc — the Church successor: constructor, value, and its β-unfold

The Church-numeral arc shipped the polymorphic numerals `churchNumeralLambda n = λA.λf.λx. f^n x` (#1007), their
faithfulness (#1006), and the general iteration computation `numeral n · A · f · x ↝* f^n x` (#1009).  What it
never shipped is the SUCCESSOR OPERATION — the function that adds one iteration.  This file introduces it:

  `churchSucc = λn. λA. λf. λx. f (n A f x)`

applies the step `f` once MORE than `n` does.  It is the foundational building block for numeral-valued
computations (a future `length : ChurchList → ChurchNat` folds with `succ`), and the natural companion to the
shipped numerals.  This file ships the constructor, proves it is a closed VALUE, and gives its first computational
step (the single β-unfold exposing the successor abstraction):

  * **`churchSucc_isStepNormalForm`** — `churchSucc` is a closed no-step normal form (a value): four `lamCell`
    wrappers over the body `f (n A f x)`, whose head `f` (`var 1`) is a variable, not a lambda — no redex.
  * **`churchSucc_betaUnfold`** — `churchSucc n ↝ λA.λf.λx. f ((weaken³ n) A f x)`: the single β-step that applies
    `churchSucc` to its numeral argument and exposes the successor abstraction (`n` lifted under the three fresh
    binders).  The reshape `succ_step1_reshape` (the n-binder substitution) computes by `rfl`.

The fully-applied iteration `churchSucc n · A · f · x ↝* f (n A f x)` — the operational-successor property that
connects `churchSucc` to the numeral iteration (#1009) — requires collapsing `n`'s weaken-tower across the three
inner β-steps (`weaken³ n → weaken² n → weaken n → n`), which does NOT compute by `rfl` and needs the
weaken-cancellation reshapes; it is the next increment in this arc (see the verification memory).

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

`churchSucc_isStepNormalForm` is `by decide` (the no-step-normal-form check is decidable on the concrete closed
term, axiom-free).  `succ_step1_reshape` is `unfold + rfl` (the first-binder substitution lifts the singleton on
the head-index and computes directly).  `churchSucc_betaUnfold` is `Step.beta` with the reshape rewritten FORWARD
at the hypothesis.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- Body of `churchSucc` under all four binders (`n`=var3, `A`=var2, `f`=var1, `x`=var0): `f (n A f x)`. -/
def succBody4 : RawTerm 4 :=
  appCell (variableCell (⟨1, by decide⟩ : Fin 4))
    (appCell (appCell (appCell (variableCell (⟨3, by decide⟩ : Fin 4))
        (variableCell (⟨2, by decide⟩ : Fin 4)))
      (variableCell (⟨1, by decide⟩ : Fin 4)))
      (variableCell (⟨0, by decide⟩ : Fin 4)))

/-- `churchSucc = λn. λA. λf. λx. f (n A f x)` — the Church successor: applies the step `f` one more time than `n`. -/
def churchSucc : RawTerm 0 :=
  lamCell (lamCell (lamCell (lamCell succBody4)))

/-- The body after substituting `numeral` for the n-binder (`var 3`), threaded under the three inner binders:
`var 3 ↦ weaken³ numeral`; `A`=var2, `f`=var1, `x`=var0 unchanged. -/
def succBody3 (numeral : RawTerm 0) : RawTerm 3 :=
  appCell (variableCell (⟨1, by decide⟩ : Fin 3))
    (appCell (appCell (appCell (RawTerm.weaken (RawTerm.weaken (RawTerm.weaken numeral)))
        (variableCell (⟨2, by decide⟩ : Fin 3)))
      (variableCell (⟨1, by decide⟩ : Fin 3)))
      (variableCell (⟨0, by decide⟩ : Fin 3)))

/-- The n-binder substitution computes by `rfl`: the lifted singleton on the head-index `var 3` yields `weaken³
numeral`, and the inner variables are unchanged. -/
theorem succ_step1_reshape (numeral : RawTerm 0) :
    RawTerm.subst0 (lamCell (lamCell (lamCell succBody4))) numeral
      = lamCell (lamCell (lamCell (succBody3 numeral))) := by
  unfold RawTerm.subst0 succBody4 succBody3
  rfl

/-- **`churchSucc` is a closed no-step normal form (a value).**  Four `lamCell` wrappers over `f (n A f x)`, whose
head `f` (`var 1`) is a variable — not a lambda — so the body heads no β-redex. -/
theorem churchSucc_isStepNormalForm : RawTerm.isStepNormalForm churchSucc := by decide

/-- **`churchSucc n ↝ λA.λf.λx. f ((weaken³ n) A f x)`** — the single β-step applying `churchSucc` to its numeral
argument and exposing the successor abstraction (`n` lifted under the three fresh binders).  The next increment is
the fully-applied iteration `churchSucc n A f x ↝* f (n A f x)`, which needs the weaken-tower cancellation. -/
theorem churchSucc_betaUnfold (numeral : RawTerm 0) :
    Step (appCell churchSucc numeral) (lamCell (lamCell (lamCell (succBody3 numeral)))) := by
  have base : Step (appCell churchSucc numeral)
      (RawTerm.subst0 (lamCell (lamCell (lamCell succBody4))) numeral) := Step.beta
  rw [succ_step1_reshape] at base
  exact base

end FX1Poly.Typed
