import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SubstPointwise

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.Composition

Semantic slice of typed pointwise substitution and composition infrastructure. -/

namespace LeanFX2

/-! ## TermSubst composition

`TermSubst.compose` builds the typed companion of `Subst.compose`.
For each source position `position`, it produces a Term in the final
target whose type/raw match the composed substitution by post-substituting
the first TermSubst's value through the second TermSubst.  The Ty
alignment uses `Ty.subst_compose`; the raw alignment is definitional
(both `Subst.compose.forRaw` and `RawTermSubst.compose` are defined
pointwise as `(σ1.forRaw p).subst σ2.forRaw`). -/

/-- Compose two TermSubsts: post-substitute the first's image through
the second.  The Ty cast aligns `(varType src pos).subst σ1).subst σ2`
with `(varType src pos).subst (Subst.compose σ1 σ2)` via the typed
two-position cast helper `Term.castType`. -/
def TermSubst.compose
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst) :
    TermSubst sourceCtx targetCtx (Subst.compose firstSubst secondSubst) :=
  fun position =>
    cast
      (by rw [Ty.subst_compose firstSubst secondSubst (varType sourceCtx position)])
      (Term.subst secondTermSubst (firstTermSubst position))

/-- The cast in `TermSubst.compose` doesn't change the Term value
underneath — only the type index.  HEq witnesses this directly via
`cast_heq`. -/
theorem TermSubst.compose_position_HEq
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst)
    (position : Fin sourceScope) :
    HEq (TermSubst.compose firstTermSubst secondTermSubst position)
        (Term.subst secondTermSubst (firstTermSubst position)) :=
  cast_heq _ _

end LeanFX2
