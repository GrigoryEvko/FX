import FX1Poly.Core.Substrate.Certifier.HasCertifiedComposition
import FX1Poly.Core.Substrate.Certifier.HasCertifiedProjections
import FX1Poly.Tier0.Syntax.RawTermSubst0
import FX1Poly.Tier0.Syntax.GenAlgebra
import FX1Poly.Tier0.Syntax.RawTermNonVarReduces

/-! # Foundation/PolyCell/Core/StructuralInductionPrimitives
   — building blocks for the structural induction over PolyCell

The **foundational primitives** the structural induction
(`HasCertifiedCellDim0.preservedBySubst`) composes:

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

The primitives here are the toolkit (b)/(c) needs.  The mutual
recursion + spine half live in `SubstPreservationMutual.lean`; each
primitive verified at zero axioms locks in a foundation that doesn't
shift under the cascade.

## Zero-axiom verification

All declarations close via `dsimp only` + `rw [dif_neg ...]` + `rfl`
or direct hypothesis application.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

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

/-! ## Section 2 — Non-var fold reductions: see `Tier0.Syntax.RawTermNonVarReduces`

`RawTerm.rename_nonVar_reduces` / `RawTerm.subst_nonVar_reduces` are pure
de Bruijn-syntax facts; they moved down to the Tier-0 syntax substrate
(imported above, re-exported here) so the `.term` consumers that need only
them no longer transitively depend on this file's `HasCertified*` profile
layer.  The certified-cell theorems below still build directly on the
variable case. -/

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

end FX1Poly.Core
