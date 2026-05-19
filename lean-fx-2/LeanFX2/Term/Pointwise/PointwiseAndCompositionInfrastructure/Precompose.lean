import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Subst

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

Pointwise equality for TermSubst plus typed substitution composition
infrastructure (compose, cast HEq scaffolding, beta-singleton consSingleton).
Foundational layer of the Pointwise cascade.

## Root status

Kernel — pointwise/composition skeleton consumed by every weaken-subst-
singleton constructor arm. -/

namespace LeanFX2

/-! ## Pre-composing typed substitutions by renamings

The beta-contractum path needs to compare "rename, then substitute" with
substituting by the corresponding input-precomposed substitution.  This
is the typed companion of `Subst.precomposeRenaming`: the raw component
is definitional, while the type index is transported through
`Ty.rename_subst_commute` and the typed renaming's variable lookup
equality. -/

/-- Pull a typed substitution back along a typed renaming on its source
context. -/
def TermSubst.precomposeRenaming
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma) :
    TermSubst sourceCtx targetCtx (Subst.precomposeRenaming rho sigma) :=
  fun position =>
    (by
      show (varType middleCtx (rho position)).subst sigma =
        (varType sourceCtx position).subst
          (Subst.precomposeRenaming rho sigma)
      rw [termRenaming position]
      exact Ty.rename_subst_commute rho sigma
        (varType sourceCtx position)) ▸
      termSubst (rho position)

end LeanFX2
