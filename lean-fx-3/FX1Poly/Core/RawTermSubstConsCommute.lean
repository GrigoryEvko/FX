import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstPointwise
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/RawTermSubstConsCommute
    — weakening cancels under a cons-extended substitution

The reducible-substitution environment for the fundamental theorem (the RC environment) extends a
closing substitution at a binder via `RawTermSubst.cons headTerm tailSubst`, and looks context types up
with `TypingContext.lookup`, which WEAKENS each stored binding type by one (`RawRenaming.weaken`).  The
two interact by CANCELLATION: substituting a `cons`-extended substitution through a once-weakened term
drops the fresh slot and reduces to the tail substitution —

  `subst (cons head tail) (rename weaken X) = subst tail X`.

This is the general (`cons`) form of the shipped singleton cancellation `RawTerm.weaken_subst_singleton`
(which is its `tail = identity` instance), and it is exactly the de Bruijn bookkeeping (§11.6.3) the RC
environment's binder-extension lemma needs at every variable.

## Zero-axiom verification

`RawTerm.rename_subst_commute` folds the rename into the substitution, then `RawTerm.subst_pointwise`
against the pointwise fact that pre-composing `weaken` with `cons head tail` drops the head and returns
`tail` (a `Fin`-position `cases` closed by `rfl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- Pre-composing canonical weakening with a `cons`-extended substitution drops the fresh head slot and
returns the tail substitution, pointwise: `(cons head tail) ∘ weaken = tail`.  The general form of
`RawTermSubst.weaken_then_singleton_pointwise` (singleton = `cons _ identity`). -/
theorem RawTermSubst.weaken_then_cons_pointwise {scope targetScope : Nat}
    (headTerm : RawTerm targetScope) (tailSubst : RawTermSubst scope targetScope) :
    RawTermSubst.PointwiseEq
      (RawRenaming.thenSubst RawRenaming.weaken (RawTermSubst.cons headTerm tailSubst))
      tailSubst := by
  intro position
  cases position with
  | mk positionValue positionBound => rfl

/-- **Weakening cancels under a `cons`-extended substitution.**  Substituting `cons head tail` through a
once-weakened term returns the tail substitution applied to the original term — the fresh binder slot
introduced by the weakening is exactly the slot `cons` fills, so they annihilate.  The general (`cons`)
form of `RawTerm.weaken_subst_singleton`; the de Bruijn step the RC environment's `cons` extension runs
at every context variable. -/
theorem RawTerm.weaken_subst_cons {scope targetScope : Nat} (sourceTerm : RawTerm scope)
    (headTerm : RawTerm targetScope) (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons headTerm tailSubst)
        (RawTerm.rename RawRenaming.weaken sourceTerm) =
      RawTerm.subst tailSubst sourceTerm := by
  rw [RawTerm.rename_subst_commute RawRenaming.weaken
    (RawTermSubst.cons headTerm tailSubst) sourceTerm]
  exact RawTerm.subst_pointwise
    (RawTermSubst.weaken_then_cons_pointwise headTerm tailSubst) sourceTerm

/-- **A `cons`-extended substitution is a `subst0` after the lifted tail** — the binder-split keystone the
fundamental theorem's `piIntro` assembly case threads.  Substituting `cons head tail` through `body` equals
lifting `tail` under the binder, substituting that into `body`, then `subst0`-ing the head:

  `subst (cons head tail) body = subst0 (subst (lift tail) body) head`.

The body induction hypothesis, taken at the binder-extended closing environment (`ReducibleEnvAt.cons`
produces the substitution `RawTermSubst.cons arg γ`), reduces `body` to `subst (cons arg γ) body`; the
semantic introduction rule (`abstractionUnderSubst` / `abstractionNonDependentUnderSubst`) consumes
`subst0 (subst (lift γ) body) arg`.  This identity is the bridge between them, and the SAME `subst0`
identity bridges the eliminated type `subst (cons arg γ) B` to the arm's `subst0 (subst (lift γ) B) arg`.

The single-substitution counterpart of `RawTerm.subst0_subst_commute`, proved by the identical
`subst_compose` + `subst_pointwise` template: at variable 0 both sides hit `head` (`rfl`); at `k + 1` both
reduce to `tail k` (`RawTerm.weaken_subst_singleton` cancels the lift's weakening against the head
singleton). -/
theorem RawTerm.subst_cons_eq_subst0_lift {scope targetScope : Nat}
    (body : RawTerm (scope + 1)) (headTerm : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons headTerm tailSubst) body =
      RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) body) headTerm := by
  dsimp only [RawTerm.subst0]
  rw [RawTerm.subst_compose (RawTermSubst.lift tailSubst)
    (RawTermSubst.singleton headTerm) body]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ priorPositionValue =>
          dsimp only [RawTermSubst.compose, RawTermSubst.singleton,
            RawTermSubst.lift, RawTermSubst.cons]
          exact (RawTerm.weaken_subst_singleton
            (tailSubst ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩)
            headTerm).symm

end FX1Poly.Core
