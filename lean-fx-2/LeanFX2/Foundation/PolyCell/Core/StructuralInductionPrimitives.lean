import LeanFX2.Foundation.PolyCell.Core.HasCertifiedComposition
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedProjections
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0
import LeanFX2.Foundation.PolyCell.Core.GenAlgebra

/-! # Foundation/PolyCell/Core/StructuralInductionPrimitives
   — building blocks for the structural induction over PolyCell

V2-L3.1 phase D step 28 (2026-05-27).  Ships the **foundational
primitives** that the future structural induction
(`HasCertifiedCellDim0.preservedBySubst`) will compose:

  1. **Shape extraction**: any `HCC source` unwraps to a
     `.mkGen generator payload children` shape via the dim-0 cell
     having only the `.gen` ctor.

  2. **Non-var fold reduction**: with `hNotVar : generator ≠ .gen_var`,
     the fold engine reduces `(.mkGen generator payload children)`
     to a clean `.mkGen generator (payload-cast) (foldChildren ...)`
     form.  This unblocks the non-var case of the structural
     induction.

  3. **Var case primitive**: when `σ` certifies every substituent,
     `subst σ (.mkGen .gen_var pos .childNil)` is certified
     (immediate from σ's hypothesis at `pos`).

## Why these matter for the structural induction

The mutual block:

```
mutual
  HasCertifiedCellDim0.preservedBySubst (cell half)
  CertifiedTermSpine.preservedBySubst   (spine half)
end mutual
```

The cell half needs to:
  (a) destructure HCC via `obtain ⟨_, cell⟩`,
  (b) `cases cell with | gen _ _ spine`,
  (c) dispatch on `generator = .gen_var` via dite:
      - var case: apply `subst_var_certify`,
      - non-var: apply `subst_nonVar_reduces` + recursive spine call
        + rebuild via `PolyCell.gen` + `.intro`.

The primitives shipped here are the toolkit (b)/(c) needs.  The
mutual recursion + spine half are the remaining (substantial)
work — but each primitive verified at zero axioms locks in a
foundation that doesn't shift under the cascade.

## Zero-axiom verification

All declarations close via `dsimp only` + `rw [dif_neg ...]` + `rfl`
or direct hypothesis application.  Spike (deleted) confirmed
`#print axioms RawTerm.subst_nonVar_spike` reports clean.
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Shape extraction from HasCertifiedCellDim0 -/

/-- **HCC unwrap to mkGen shape.**

At dim 0, every `PolyCell` is the `.gen` constructor (the only
ctor producing dim 0 in PolyCell's inductive).  Combined with
HasCertifiedCellDim0's existential destructure, this exposes
the source's `.mkGen generator payload children` shape. -/
theorem HasCertifiedCellDim0.mkGen_shape
    {profile : PolyProfile} {scope : Nat} {source : RawTerm scope}
    (cert : HasCertifiedCellDim0 (profile := profile) source) :
    ∃ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope),
      source = .mkGen generator payload children := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | @gen _ generator payload children _ _ _ =>
    exact ⟨generator, payload, children, rfl⟩

/-! ## Section 2 — Non-var fold reductions (rename + subst) -/

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

/-! ## Section 3 — Variable case primitives -/

/-- **Var subst certify.**

When every substituent in `σ` is certified, subst on a variable
is certified.  This is the **var case** of the structural induction:
`subst σ (.mkGen .gen_var pos .childNil) = σ pos` (by rfl via the
fold's var arm + the ActsOnRawTermVar bridge for RawTermSubst),
and `σ pos` is certified by hypothesis. -/
theorem HasCertifiedCellDim0.subst_var_certify
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCertify : ∀ (idx : Fin srcScope),
      HasCertifiedCellDim0 (profile := profile) (sigma idx))
    (varPos : Fin srcScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst sigma
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope)) := by
  show HasCertifiedCellDim0 (profile := profile) (sigma varPos)
  exact sigmaCertify varPos

/-- **Rename var certify.**

Sibling of `subst_var_certify` for renaming: `rename ρ` on a
variable is `.mkGen .gen_var (ρ pos) .childNil`, which is
certified via `HasCertifiedCellDim0.var`. -/
theorem HasCertifiedCellDim0.rename_var_certify
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    (varPos : Fin srcScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope)) := by
  show HasCertifiedCellDim0 (profile := profile)
    (.mkGen .gen_var (rho varPos) .childNil)
  exact HasCertifiedCellDim0.var (rho varPos)

end LeanFX2.Foundation.PolyCell.Core
