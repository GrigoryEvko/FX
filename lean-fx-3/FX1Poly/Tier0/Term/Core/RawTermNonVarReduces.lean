import FX1Poly.Tier0.Term.Subst.RawTermSubst0
import FX1Poly.Tier0.Term.Generator.GenAlgebra

/-! # FX1Poly/Tier0/Syntax/RawTermNonVarReduces — non-var fold reductions

The two `RawTerm.rename` / `RawTerm.subst` reduction equations for the
NON-variable case: when a cell's head generator is not `gen_var`, the fold
engine dispatches into its else-branch and the result is structurally the
same `.mkGen` with the children folded pointwise.

These are pure de Bruijn-syntax facts — they depend ONLY on the Tier-0
syntax substrate (`RawTerm`, the canonical `GenAlgebra`, `fold`/`foldChildren`)
and reference no typing or certified-cell machinery.  They were split out of
`Core.StructuralInductionPrimitives` (which keeps the `HasCertifiedCellDim0`
theorems that genuinely sit above Core) so the `.term` consumers that need
only these reductions — `RawTermFresh`, `RawTermRenameAsSubst`, and their
downstream — depend on Tier-0 syntax alone rather than reaching up through
`HasCertified*` into the profile-assembly layer.

Declared in `namespace FX1Poly.Core` to preserve the existing qualified names
(`RawTerm.rename_nonVar_reduces` / `RawTerm.subst_nonVar_reduces`), so every
consumer needs only its `import` line repointed, not its references.
-/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

/-- **Rename's non-var fold reduction.**

For `generator ≠ .gen_var`, the fold engine's dispatch falls into
the non-var branch.  The result is `.mkGen generator (payload-cast)
(foldChildren ρ children)`.

Closes via `dsimp only [fold]` to expose the dite, then
`rw [dif_neg hNotVar]` to take the else branch, then `rfl`
to unfold the canonical algebra's `mkGen` application. -/
theorem RawTerm.rename_nonVar_reduces
    {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    {generator : Generator}
    (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload srcScope)
    (children : RawTermChildren generator.binderShifts srcScope) :
    RawTerm.rename rho (.mkGen generator payload children) =
      .mkGen generator
        (Generator.payload_scope_invariant_of_not_var hNotVar
          srcScope tgtScope ▸ payload)
        (foldChildren GenAlgebra.canonical rho children) := by
  show fold GenAlgebra.canonical rho
        (.mkGen generator payload children) = _
  dsimp only [fold]
  rw [dif_neg hNotVar]
  rfl

/-- **Subst's non-var fold reduction.**

Symmetric to `rename_nonVar_reduces`: same dispatch, same shape,
just with the substitution container instead of renaming. -/
theorem RawTerm.subst_nonVar_reduces
    {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    {generator : Generator}
    (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload srcScope)
    (children : RawTermChildren generator.binderShifts srcScope) :
    RawTerm.subst sigma (.mkGen generator payload children) =
      .mkGen generator
        (Generator.payload_scope_invariant_of_not_var hNotVar
          srcScope tgtScope ▸ payload)
        (foldChildren GenAlgebra.canonical sigma children) := by
  show fold GenAlgebra.canonical sigma
        (.mkGen generator payload children) = _
  dsimp only [fold]
  rw [dif_neg hNotVar]
  rfl

end FX1Poly.Core
