import LeanFX2.Term.Subst

/-! # LeanFX2.Term.SubstTargetCtxCast  (cross-sigma binder-bridge support)

Two cast-innocence lemmas: rewriting a `TermSubst`'s *target-context* index by a
propositional `Eq` leaves the substitution result (resp. the per-position entry)
heterogeneously unchanged.

These confine the index divergence that appears in the binder arms of the
cross-sigma `Term.subst_pointwise_HEq` bridge.  `TermSubst.lift` bakes the
substituted domain type `newSourceType.subst sigma` into its target context,
so two pointwise-equal substitutions `sigma1`, `sigma2` produce lifts living in
the propositionally-but-not-definitionally equal contexts
`targetCtx.cons (domainType.subst sigma1)` and `targetCtx.cons (domainType.subst
sigma2)`.  Rather than generalise the whole bridge to two target contexts (which
would force every non-binder arm to juggle the divergence and break the shared
`_HEq_congr` reuse), the binder arm casts the second lift back onto the first's
target context with `targetCtxEq ▸ _`, and these lemmas certify the cast is
substitution-innocent — so the shared-context induction hypothesis still fires.

Both proofs are pure `cases` on the context equality followed by `HEq.rfl`:
axiom-clean (`Eq.rec`, no `propext` / `Quot.sound` / `Classical.choice`). -/

namespace LeanFX2

/-- Casting a typed substitution's target context by an equality leaves the
substitution result heterogeneously unchanged. -/
theorem Term.subst_targetCtx_cast_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx1 targetCtx2 : Ctx mode level targetScope}
    (targetCtxEq : targetCtx1 = targetCtx2)
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx1 sigma)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    HEq (Term.subst (targetCtxEq ▸ termSubst) someTerm)
        (Term.subst termSubst someTerm) := by
  cases targetCtxEq
  exact HEq.rfl

/-- Casting a typed substitution's target context by an equality leaves each
per-position entry heterogeneously unchanged. -/
theorem TermSubst.targetCtx_cast_entry_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx1 targetCtx2 : Ctx mode level targetScope}
    (targetCtxEq : targetCtx1 = targetCtx2)
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx1 sigma)
    (position : Fin sourceScope) :
    HEq ((targetCtxEq ▸ termSubst) position) (termSubst position) := by
  cases targetCtxEq
  exact HEq.rfl

end LeanFX2
