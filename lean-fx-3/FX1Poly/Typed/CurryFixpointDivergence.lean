import FX1Poly.Typed.UnboundedGrowthNotStronglyNormalizing
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/CurryFixpointDivergence — the parameterized Curry fixpoint Ω_g unfolds and diverges

`UntypedOmegaNotStronglyNormalizing` (#950) exhibits the bare Ω = `(λx. x x)(λx. x x)`, and
`UnboundedGrowthNotStronglyNormalizing` (#960) exhibits a growing divergence.  This file generalizes BOTH to the
**Curry fixpoint core** parameterized over an arbitrary closed term `g`:

  `Ω_g = (λx. g (x x)) (λx. g (x x))`

and proves the two facts that make it the engine of Curry's fixpoint combinator:

  * **`curryOmega_step` (★)** — the FIXPOINT UNFOLDING: `Ω_g` β-reduces in ONE step to `g (Ω_g)`.  So `Ω_g` is a
    reduction fixpoint of `g`: applying `g` to it is the same (up to a single β-step) as `Ω_g` itself.  This is
    exactly the defining property of the Curry/Turing fixpoint operator `fix g = g (fix g)`, witnessed here at
    the reduction level for the self-replicating core.  The contractum is `subst0 (g (x x)) (λx.g(xx))`; the
    weakened `g` survives the substitution (`weaken_subst_singleton`, the `subst0 (weaken g) arg = g`
    cancellation) and the `x x` recopies the abstraction, yielding `g (Ω_g)` on the nose.

  * **`curryOmega_notStronglyNormalizing` (★)** — DIVERGENCE for EVERY `g`: `Ω_g ↝ g Ω_g ↝ g (g Ω_g) ↝ …`
    grows without bound, so it is never strongly normalizing.  Hence every term `g` carries a non-terminating
    fixpoint, which is precisely why a general fixpoint operator is UNTYPABLE in the SN engine — `SN-043`
    (`HasTypeDescPi Γ t T → IsStronglyNormalizing t`, #546) would otherwise be contradicted.  The witness is the
    strictly-growing sequence `g^n (Ω_g)` fed through the general infinite-reduction principle (#960).

Bare Ω is the degenerate special case (no `g` wrapper); the `g`-parameterization shows the divergence is
uniform and is the load-bearing reason the calculus needs typing to normalize.  Everything is about the raw
`Step` relation — no typing derivation is consulted.

## Zero-axiom verification

`curryOmega_step` is a single `Step.beta` whose contractum is rewritten to `g (Ω_g)` via
`RawTerm.weaken_subst_singleton` (the rest of the substitution computes definitionally).  The divergent sequence
steps by the fixpoint unfolding at index 0 and an argument-position congruence (`Step.cong .gen_app ()` +
`StepChildren.there`/`StepChildren.here`, scopes pinned explicitly) at `index+1`; non-SN follows from the shipped
`notStronglyNormalizing_of_infiniteReduction` (#960).  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `λx. g (x x)` — the Curry self-applicator parameterized by `g`, with `g` weakened into the binder scope. -/
def curryHalf (g : RawTerm 0) : RawTerm 0 :=
  lamCell (.mkGen .gen_unit () .childNil)
    (appCell (RawTerm.weaken g)
      (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

/-- `Ω_g = (λx. g (x x)) (λx. g (x x))` — the Curry fixpoint core for `g`.  With a trivial `g` it is Ω. -/
def curryOmega (g : RawTerm 0) : RawTerm 0 :=
  appCell (curryHalf g) (curryHalf g)

/-- ★ **The Curry fixpoint UNFOLDING: `Ω_g ↝ g (Ω_g)`.**  `Ω_g` β-reduces in one step to `g` applied to itself,
so it is a reduction fixpoint of `g` (Curry's `fix g = g (fix g)` at the self-replicating core).  The redex
contracts to `subst0 (g (x x)) (λx.g(xx))`; the weakened `g` survives the substitution
(`weaken_subst_singleton`) and the `x x` recopies the abstraction, giving `g (Ω_g)` exactly. -/
theorem curryOmega_step (g : RawTerm 0) : Step (curryOmega g) (appCell g (curryOmega g)) := by
  have betaStep : Step (curryOmega g)
      (RawTerm.subst0 (appCell (RawTerm.weaken g)
        (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) (curryHalf g)) := Step.beta
  have contractumEq :
      RawTerm.subst0 (appCell (RawTerm.weaken g)
        (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) (curryHalf g)
        = appCell g (curryOmega g) := by
    show appCell (RawTerm.subst (RawTermSubst.singleton (curryHalf g)) (RawTerm.weaken g)) (curryOmega g)
      = appCell g (curryOmega g)
    rw [RawTerm.weaken_subst_singleton]
  rw [contractumEq] at betaStep
  exact betaStep

/-- The strictly-growing reduction sequence out of `Ω_g`: the `(n+1)`-th term wraps the `n`-th in one more
`g`-application (`g^n (Ω_g)`). -/
def curryDivergentSequence (g : RawTerm 0) : Nat → RawTerm 0
  | 0 => curryOmega g
  | k + 1 => appCell g (curryDivergentSequence g k)

/-- Every term in the divergent sequence steps to the next: index `0` is the fixpoint unfolding
(`curryOmega_step`); index `k+1` is an argument-position congruence step (`Step.cong .gen_app ()` into the second
child via `StepChildren.there`/`StepChildren.here`) carrying the inductive step. -/
theorem curryDivergentSequence_steps (g : RawTerm 0) :
    ∀ index, Step (curryDivergentSequence g index) (curryDivergentSequence g (index + 1))
  | 0 => curryOmega_step g
  | k + 1 =>
    Step.cong .gen_app ()
      (StepChildren.there (parentScope := 0) (headShift := 0) (restShifts := [0]) g
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [])
          .childNil (curryDivergentSequence_steps g k)))

/-- ★ **`Ω_g` is NOT strongly normalizing — for ANY `g`.**  It diverges by unbounded growth
(`Ω_g ↝ g Ω_g ↝ g (g Ω_g) ↝ …`), witnessed by its strictly-growing infinite reduction sequence through the
general `notStronglyNormalizing_of_infiniteReduction` principle (#960).  So every term carries a non-terminating
Curry fixpoint — exactly why a general fixpoint operator is untypable in the SN engine (`SN-043`, #546): typing
is precisely what excludes these self-replicating terms. -/
theorem curryOmega_notStronglyNormalizing (g : RawTerm 0) :
    ¬ IsStronglyNormalizing (curryOmega g) :=
  notStronglyNormalizing_of_infiniteReduction (curryDivergentSequence g)
    (curryDivergentSequence_steps g)

end FX1Poly.Typed
