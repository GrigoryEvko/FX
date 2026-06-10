import FX1Poly.Typed.CombinatoryCompleteness
import FX1Poly.Core.RawTermSubstLiftWeaken

/-! # FX1Poly/Typed/SymbolicSCombinatorRule — the general S-combinator rule `S a b c ↝* (a c)(b c)`

`CombinatoryCompleteness` (#1015/#1016) shipped `skkReducesToIdentity` (`S K K x ↝* x`) but explicitly DEFERRED
the fully general S-rule for SYMBOLIC arguments — its docstring notes that "with symbolic arguments the
intermediate `subst (lift (singleton b)) (weaken² a)` does not reduce to `weaken a` by `rfl`".  That double-weaken
cancellation is now a shipped lemma (`RawTerm.subst_lift_singleton_weaken_weaken`, #1023), so the general rule is
straightforward assembly:

  **`combinatorS_reduces` (★)** — for EVERY closed (symbolic) `a, b, c`:
  `S a b c  ↝*  (a c)(b c)`.  The classic S-combinator law, the last deferred symbolic combinator reduction.

The three β-steps reuse the shipped intermediate reducts `saTerm`/`sabTerm`:

  * **β1 (`S a → saTerm a`)** — `Step.beta` directly: `saTerm a = λy.λz. ((weaken² a) z)(y z)` is the
    `rfl`-definitional contractum of `subst0` substituting `a` for `x` (the variable `x` sits under two binders,
    so it becomes `weaken² a` by a structural lift-lookup — no symbolic obstruction).
  * **β2 (`saTerm a · b → sabTerm a b`)** via `saTermBody_subst_b` — the contractum reshape that USES the
    double-weaken cancellation: substituting `b` for `y` turns `weaken² a` (under the remaining `z` binder) into
    `weaken a` (`subst (lift (singleton b)) (weaken² a) = weaken a`, #1023) and `y` into `weaken b`, yielding
    `sabTerm a b = λz. ((weaken a) z)((weaken b) z)`.
  * **β3 (`sabTerm a b · c → (a c)(b c)`)** via `sabTermBody_subst_c` — the final reshape: substituting `c` for
    `z` cancels each single weakening (`weaken_subst_singleton`: `subst0 (weaken a) c = a`), giving
    `((a) c)((b) c)`.

This closes the unmet half of #1016's claim and DEMONSTRATES that the de Bruijn substitution substrate is now
complete: the single-weaken cancellation (`weaken_subst_singleton`, used here in β3) and the double-weaken
cancellation (`subst_lift_singleton_weaken_weaken`, used in β2) together make every β-redex contractum reshape
over a closed/symbolic argument mechanical.

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

β1 is `Step.beta` (its contractum is `rfl`-definitional).  The β2 / β3 reshapes are `show` (re-expressing the
contractum with `subst` distributed through `appCell`/`lamCell` — definitional) + `rw` of the double-weaken
(`subst_lift_singleton_weaken_weaken`) resp. single-weaken (`weaken_subst_singleton`) cancellation + `rfl` for the
residual variable substitutions.  The reduction lifts the β-steps through function-position congruences
(`Step.cong .gen_app ()` + `StepChildren.here` with explicit scopes) and composes by `StepStar.trans`.  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- **β2 contractum reshape.**  Substituting the step `b` for `y` in `saTerm a`'s body yields `sabTerm a b` — the
`weaken² a` under the remaining `z` binder collapses to `weaken a` via the double-weaken cancellation
(`subst_lift_singleton_weaken_weaken`, #1023), `y` becomes `weaken b`.  The reshape the concrete `SKK` proof got
for free by `rfl` but symbolic arguments need this lemma for. -/
theorem saTermBody_subst_b (a b : RawTerm 0) :
    RawTerm.subst0
        (lamCell combinatorDomainAnn (appCell
          (appCell (RawTerm.weaken (RawTerm.weaken a)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
          (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) b
      = sabTerm a b := by
  dsimp only [RawTerm.subst0, sabTerm]
  show lamCell combinatorDomainAnn (appCell
      (appCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton b))
        (RawTerm.weaken (RawTerm.weaken a))) _) _) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken a b]
  rfl

/-- **β3 contractum reshape.**  Substituting the argument `c` for `z` in `sabTerm a b`'s body cancels each single
weakening (`weaken_subst_singleton`), yielding `(a c)(b c)`. -/
theorem sabTermBody_subst_c (a b c : RawTerm 0) :
    RawTerm.subst0
        (appCell (appCell (RawTerm.weaken a) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (appCell (RawTerm.weaken b) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) c
      = appCell (appCell a c) (appCell b c) := by
  dsimp only [RawTerm.subst0]
  show appCell (appCell (RawTerm.subst (RawTermSubst.singleton c) (RawTerm.weaken a)) _)
      (appCell (RawTerm.subst (RawTermSubst.singleton c) (RawTerm.weaken b)) _) = _
  rw [RawTerm.weaken_subst_singleton a c, RawTerm.weaken_subst_singleton b c]
  rfl

/-- ★ **The general S-combinator rule.**  For every closed `a, b, c`, `S a b c ↝* (a c)(b c)` — the step `a` and
the step `b` are each applied to the argument `c`, and the results applied.  The last deferred symbolic combinator
reduction (the unmet half of #1016, which shipped only the concrete `S K K x ↝* x`): the general rule follows
from the #1023 double-weaken cancellation by pure assembly. -/
theorem combinatorS_reduces (a b c : RawTerm 0) :
    StepStar (appCell (appCell (appCell combinatorS a) b) c)
      (appCell (appCell a c) (appCell b c)) := by
  have step1 : Step (appCell combinatorS a) (saTerm a) := Step.beta
  have step2 : Step (appCell (saTerm a) b) (sabTerm a b) := by
    rw [← saTermBody_subst_b a b]; exact Step.beta
  have step3 : Step (appCell (sabTerm a b) c) (appCell (appCell a c) (appCell b c)) := by
    rw [← sabTermBody_subst_c a b c]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons c .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons b .childNil) step1))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          (.childCons c .childNil) step2))
      (StepStar.trans step3 (StepStar.refl _)))

end FX1Poly.Typed
