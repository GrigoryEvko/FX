import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/CurryFixpointCombinator — the Curry fixpoint combinator and its fixpoint property

`CurryFixpointDivergence` (#1013) built the applied core `Ω_g = (λx. g(x x))(λx. g(x x))` with `Ω_g ↝ g(Ω_g)`.
This file closes the story with the actual **Curry Y combinator** — a single closed term that produces `Ω_g`
from `g`:

  `fix = λf. (λx. f (x x)) (λx. f (x x))`

  * **`fixCombinator_applied_step`** — `fix g` β-reduces to `Ω_g`: the body's bound `f` is replaced by `g`, and
    the under-binder substitution `subst0 fixInnerHalf g` computes to `curryHalf g` DEFINITIONALLY (the lifted
    singleton sends the inner de Bruijn `1` to `weaken g`, by `rfl` — no auxiliary lemma needed).

  * **`fixCombinator_isFixpoint` (★)** — THE FIXPOINT PROPERTY: `fix g` is convertible to `g (fix g)`.  Both sides
    reduce to the common term `g (Ω_g)` (`fix g` in two steps: instantiation β then the unfolding `Ω_g ↝ g(Ω_g)`;
    `g (fix g)` in one argument-congruence step), so they are definitionally equal.  This is the defining
    equation of a fixpoint combinator, `fix g =_β g (fix g)` — the FX raw calculus has general recursion.

  * **`fixCombinator_applied_notStronglyNormalizing`** — `fix g` diverges for every `g` (it steps to the
    non-terminating `Ω_g`, and a reduct of an SN term would be SN).

Together: the untyped FX term calculus is Turing-complete (carries a fixpoint combinator), and every `fix g`
diverges — which is precisely why the type system is indispensable for strong normalization (`SN-043`, #546).
Everything is the raw `Step`/`Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

`fixCombinator_applied_step` is a single `Step.beta` (the under-binder substitution is `rfl`-definitional).
`fixCombinator_isFixpoint` assembles two `Conv.fromStepStar` reductions to the common reduct via
`Conv.trans`/`Conv.sym`, with the right side's one step an argument-position congruence
(`Step.cong .gen_app ()` + `StepChildren.there`/`StepChildren.here`, scopes pinned).
`fixCombinator_applied_notStronglyNormalizing` uses `Acc.inv` (strong normalization is accessibility under the
reversed step) against `curryOmega_notStronglyNormalizing` (#1013).  No `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `λx. f (x x)` at scope 1: `f` is the outer-bound variable (de Bruijn 1), `x` the inner (de Bruijn 0). -/
def fixInnerHalf : RawTerm 1 :=
  lamCell (.mkGen .gen_unit () .childNil)
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))

/-- The Curry fixpoint combinator `fix = λf. (λx. f(x x)) (λx. f(x x))`. -/
def fixCombinator : RawTerm 0 :=
  lamCell (.mkGen .gen_unit () .childNil)
    (appCell fixInnerHalf fixInnerHalf)

/-- Applying `fix` to `g` β-reduces to `Ω_g`: the body's `f` is replaced by `g`, and the under-binder
substitution `subst0 fixInnerHalf g` computes to `curryHalf g` definitionally (the lifted singleton sends the
inner de Bruijn `1` to `weaken g`, by `rfl`). -/
theorem fixCombinator_applied_step (g : RawTerm 0) :
    Step (appCell fixCombinator g) (curryOmega g) :=
  HeadStep.beta.toStep

/-- `fix g ↝* g (Ω_g)` in two steps: the instantiation β, then the fixpoint unfolding `Ω_g ↝ g(Ω_g)`. -/
theorem fixCombinator_reducesToUnfolding (g : RawTerm 0) :
    StepStar (appCell fixCombinator g) (appCell g (curryOmega g)) :=
  StepStar.trans (fixCombinator_applied_step g)
    (StepStar.trans (curryOmega_step g) (StepStar.refl _))

/-- ★ **The FIXPOINT PROPERTY: `fix g` is convertible to `g (fix g)`.**  Both reduce to the common term
`g (Ω_g)` — `fix g` in two steps (instantiation β then the unfolding `Ω_g ↝ g(Ω_g)`), `g (fix g)` in one
argument-congruence step — so they are definitionally equal.  The defining equation of a fixpoint combinator,
`fix g =_β g (fix g)`: the FX raw calculus has general recursion. -/
theorem fixCombinator_isFixpoint (g : RawTerm 0) :
    Conv (appCell fixCombinator g) (appCell g (appCell fixCombinator g)) := by
  have rightStep : Step (appCell g (appCell fixCombinator g)) (appCell g (curryOmega g)) :=
    Step.cong .gen_app ()
      (StepChildren.there (parentScope := 0) (headShift := 0) (restShifts := [0]) g
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [])
          .childNil (fixCombinator_applied_step g)))
  exact Conv.trans (Conv.fromStepStar (fixCombinator_reducesToUnfolding g))
    (Conv.sym (Conv.fromStepStar (StepStar.trans rightStep (StepStar.refl _))))

/-- `fix g` is NOT strongly normalizing for any `g`: it steps to the non-terminating `Ω_g`, so it inherits the
divergence (a reduct of an SN term would itself be SN — strong normalization is accessibility under the reversed
step, so `Acc.inv` carries it).  Every general-recursion fixpoint diverges — the reason typing is indispensable
for `SN-043` (#546). -/
theorem fixCombinator_applied_notStronglyNormalizing (g : RawTerm 0) :
    ¬ IsStronglyNormalizing (appCell fixCombinator g) :=
  fun stronglyNormalizing =>
    curryOmega_notStronglyNormalizing g (stronglyNormalizing.inv (fixCombinator_applied_step g))

end FX1Poly.Typed
