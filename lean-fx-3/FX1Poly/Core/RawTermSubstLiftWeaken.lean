import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstRenameCommute

/-! # FX1Poly/Core/RawTermSubstLiftWeaken — the lift-weaken naturality + double-weaken cancellation

`RawTermSubst0Commute` shipped the SINGLE-weaken cancellation `weaken_subst_singleton`
(`subst (singleton arg) (weaken t) = t`).  That suffices for any β-reduction where each bound variable is
weakened AT MOST ONCE — the case the general Church-numeral computation (#1009) falls into.  But a bound variable
that occurs under TWO binders is weakened TWICE, and the resulting `subst (lift σ) (weaken² a) = weaken a`
cancellation was the one remaining de Bruijn obstruction repeatedly deferred for SYMBOLIC arguments — it blocks
the symbolic S-combinator rule (`S a b c ↝* (a c)(b c)`, the unmet residual of #1016) and the symbolic Church
sums (#1019/#1020 used a concrete stored value to dodge it).

This file proves that the obstruction is NOT a wall — it is two lemmas over the shipped substitution machinery:

  * **`subst_lift_weaken` (★)** — the lift-weaken NATURALITY: `subst (lift σ) (weaken t) = weaken (subst σ t)`.
    The substitution `lift σ` commutes with weakening.  Proof: rewrite both `weaken`s to `rename weaken`
    (`weaken_eq_rename`), apply `rename_subst_commute` to the LHS and `subst_rename_commute` to the RHS, and
    observe the two resulting composite substitutions agree POINTWISE — both send index `k` to `weaken (σ k)`
    (`weaken.thenSubst (lift σ)` at `k` is `(lift σ)(k+1) = weaken (σ k)`; `σ.postRename weaken` at `k` is
    `rename weaken (σ k) = weaken (σ k)`) — so `subst_pointwise` closes it.

  * **`subst_lift_singleton_weaken_weaken`** — the DOUBLE-weaken cancellation:
    `subst (lift (singleton outerArg)) (weaken² innerArg) = weaken innerArg`.  Two lines: `subst_lift_weaken`
    pushes the outer `lift (singleton outerArg)` past one `weaken` to `weaken (subst (singleton outerArg)
    (weaken innerArg))`, and `weaken_subst_singleton` collapses the inner `subst (singleton outerArg)
    (weaken innerArg)` to `innerArg`.

Together with the single-weaken cancellation, every β-redex contractum reshape over a closed (symbolic) argument
is now mechanical — the symbolic S-rule and symbolic Church sums become assembly (subst-push through the cell
formers, then these cancellations), with no new de Bruijn lemma.

## Zero-axiom verification

`subst_lift_weaken` is `weaken_eq_rename` rewrites + `rename_subst_commute` + `subst_rename_commute` +
`subst_pointwise` with a `rfl` pointwise body; `subst_lift_singleton_weaken_weaken` is two `rw`s.  No `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- ★ **The lift-weaken naturality.**  `subst (lift σ) (weaken t) = weaken (subst σ t)` — lifting a substitution
commutes with weakening.  Both composites send index `k` to `weaken (σ k)`, so the two `rename`/`subst` reorderings
agree pointwise. -/
theorem RawTerm.subst_lift_weaken {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (RawTermSubst.lift someSubstitution) (RawTerm.weaken sourceTerm)
      = RawTerm.weaken (RawTerm.subst someSubstitution sourceTerm) := by
  rw [RawTerm.weaken_eq_rename sourceTerm,
    RawTerm.weaken_eq_rename (RawTerm.subst someSubstitution sourceTerm)]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken (RawTermSubst.lift someSubstitution) sourceTerm]
  rw [RawTerm.subst_rename_commute someSubstitution RawRenaming.weaken sourceTerm]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound => rfl

/-- **The double-weaken cancellation.**  `subst (lift (singleton outerArg)) (weaken² innerArg) = weaken innerArg`
— substituting a lifted singleton through a doubly-weakened term cancels exactly one weakening.  The reshape that
unblocks the symbolic S-combinator rule and symbolic Church sums (a variable under two binders is weakened twice).
`subst_lift_weaken` peels one weakening; `weaken_subst_singleton` cancels the inner singleton substitution. -/
theorem RawTerm.subst_lift_singleton_weaken_weaken {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton outerArg))
        (RawTerm.weaken (RawTerm.weaken innerArg))
      = RawTerm.weaken innerArg := by
  rw [RawTerm.subst_lift_weaken (RawTermSubst.singleton outerArg) (RawTerm.weaken innerArg)]
  rw [RawTerm.weaken_subst_singleton innerArg outerArg]

end FX1Poly.Core
