import FX1Poly.Core.CandidateReducibleSubst
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstPointwise

/-! # Foundation/PolyCell/Core/RawTermSubstConsCommute
    — weakening cancels under a cons-extended substitution

The reducible-substitution environment for the fundamental theorem (the #425 RC environment) extends a
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

end FX1Poly.Core
