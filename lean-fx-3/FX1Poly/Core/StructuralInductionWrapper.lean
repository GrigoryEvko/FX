import FX1Poly.Core.StructuralInductionPrimitives

/-! # Foundation/PolyCell/Core/StructuralInductionWrapper
   — wrapper patterns for the structural induction

Sibling to `StructuralInductionPrimitives`; the WRAPPER theorems that
factor the public-facing `HCC` preservation into:

  * Outer wrapper (this file): destructure HCC, call a Type-level
    cell renamer/substituter, wrap back into HCC.intro.
  * Inner cell renamer/substituter: the mutual `def` block over
    PolyCell + spine producing the new cell directly
    (`SubstPreservationMutual.lean`).

## What this file provides (2 declarations)

  * `HCC.preservedByRename_via_renamer` — given an abstract cell
    renamer (Type-level), produce HCC preservation.
  * `HCC.preservedBySubst_via_substituter` — sibling for subst.

Both work via the pattern:

```
obtain ⟨sort, cell⟩ := cert
exact .intro sort (cellOp cell)
```

The destructure is OK because `HCC` is a single-ctor Prop;
extracting `cell : PolyCell` (Type) is valid as INPUT to produce
a new HCC (Prop output).

## Why this matters

The full structural induction is a mutual `def` block over
PolyCell + CertifiedTermSpine (both Type), with a third
mutual partner for the binder lift (subst only).  Plugging
that `def` into THIS wrapper closes the public-facing HCC
preservation.

This separation lets the mutual block be designed independently;
this wrapper is the public HCC entry point.

## Zero-axiom verification

Each wrapper is a 2-line proof using `obtain` + `exact .intro`.
The abstract operation hypothesis is what the mutual block
provides.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **Outer wrapper for rename preservation.**

Given an abstract Type-level cell renamer, produce the public-
facing HCC preservation by destructuring + wrapping.

Plug the mutual structural induction's `PolyCell.rename_dim0` def
(`SubstPreservationMutual.lean`) into the `cellRenamer` parameter to
get HCC preservation END-TO-END. -/
theorem HasCertifiedCellDim0.preservedByRename_via_renamer
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    (cellRenamer :
      ∀ {sort : CellSort} {source : RawTerm srcScope},
        PolyCell profile sort 0 srcScope CellBoundary.trivial
          (.termBase source) →
        PolyCell profile sort 0 tgtScope CellBoundary.trivial
          (.termBase (RawTerm.rename rho source)))
    {source : RawTerm srcScope}
    (cert : HasCertifiedCellDim0 (profile := profile) source) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho source) := by
  obtain ⟨sort, cell⟩ := cert
  exact .intro sort (cellRenamer cell)

/-- **Outer wrapper for substitution preservation.**

Sibling of `preservedByRename_via_renamer` for substitution.
Same destructure-and-wrap pattern.

Plug the mutual structural induction's `PolyCell.subst_dim0` def
(`SubstPreservationMutual.lean`) in to close HCC preservation under
substitution. -/
theorem HasCertifiedCellDim0.preservedBySubst_via_substituter
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (cellSubstituter :
      ∀ {sort : CellSort} {source : RawTerm srcScope},
        PolyCell profile sort 0 srcScope CellBoundary.trivial
          (.termBase source) →
        PolyCell profile sort 0 tgtScope CellBoundary.trivial
          (.termBase (RawTerm.subst sigma source)))
    {source : RawTerm srcScope}
    (cert : HasCertifiedCellDim0 (profile := profile) source) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst sigma source) := by
  obtain ⟨sort, cell⟩ := cert
  exact .intro sort (cellSubstituter cell)

end FX1Poly.Core
