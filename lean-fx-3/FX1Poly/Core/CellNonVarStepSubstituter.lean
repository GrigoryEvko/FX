import FX1Poly.Core.StructuralInductionPrimitives
import FX1Poly.Core.GeneratorChildSpecsDim0

/-! # Foundation/PolyCell/Core/CellNonVarStepSubstituter
   — abstract non-recursive cell substituter step (subst-direction sibling)

Subst-direction sibling of `CellNonVarStepRenamer.lean`.  Ships the
**cell-side inductive step** of the structural-induction mutual block
for substitution preservation — packaged as NON-RECURSIVE definitions
that take the pre-substituted spine (for non-var) or a certified
substituent (for var) as input.

## What this ships

Two Type-valued definitions closing the cell side of the subst
mutual block:

  * `PolyCell.subst_dim0_nonVarStep` — for a non-var generator,
    given a pre-substituted spine, rebuild the parent cell at the
    target scope.  Body of `subst_dim0`'s non-var arm.

  * `PolyCell.subst_dim0_varStep` — for the var case, return the
    substituent cell directly.  Caller supplies it: `sigma`'s output
    at the given `varPos` is the new cell.

## Why this matters

Mirrors the rename-direction step renamers so the SR umbrella has
matched infrastructure for both directions.  Subject Reduction's
β-arm closes by combining:

  1. Project body's HCC + arg's HCC from the source cert.
  2. Recursively substitute body's children via the spine substituter
     mutual block.
  3. Rebuild via `PolyCell.subst_dim0_nonVarStep` (this file's
     non-var helper) OR return arg via the `varStep`.

With both step renamers and step substituters in place, the mutual
block's body is a thin dispatcher.

## Var case design

The var case is interesting: under `RawTerm.subst σ`, a variable
`var pos` reduces to `σ pos` — i.e., the substituent.  So
`subst_dim0_varStep` takes the substituent CELL (not HCC) as input
and produces it unchanged at sort `.term`, dim 0, trivial boundary.

Sibling of `HasCertifiedCellDim0.subst_var_certify` from
StructuralInductionPrimitives (which works at the HCC level).

## Zero-axiom verification

Both helpers compose `subst_nonVar_reduces`,
`Generator.gen_var.payload_scope_invariant_of_not_var`, and the
`PolyCell.gen` constructor.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **Cell-level subst step for the non-var case.**

Given:
  * a non-var generator `generator ≠ .gen_var`,
  * its payload and (original) children at source scope,
  * the SupportedGenerator admission witness,
  * the SUBSTITUTED spine (the spine substituter's output at target scope),

produces the substituted cell at the target scope.

Body of `PolyCell.subst_dim0`'s non-var arm. -/
def PolyCell.subst_dim0_nonVarStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    {generator : Generator}
    (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload srcScope)
    (children : RawTermChildren generator.binderShifts srcScope)
    (admission : SupportedGenerator generator)
    (substitutedSpine :
      CertifiedTermSpine profile generator.childSpecs tgtScope
        generator.binderShifts
        (foldChildren GenAlgebra.canonical sigma children)) :
    PolyCell profile generator.cellSort 0 tgtScope CellBoundary.trivial
      (.termBase (RawTerm.subst sigma
        (.mkGen generator payload children : RawTerm srcScope))) := by
  rw [RawTerm.subst_nonVar_reduces sigma hNotVar payload children]
  exact PolyCell.gen admission
    (genPayloadEvidence (generator := generator) (scope := tgtScope) _)
    substitutedSpine

/-- **Cell-level subst step for the var case.**

For `generator = .gen_var`, the substitution returns the substituent
directly: `RawTerm.subst σ (.mkGen .gen_var pos .childNil) = σ pos`.
Caller supplies the substituent's cell at the target scope.

Sibling of `HasCertifiedCellDim0.subst_var_certify` from
StructuralInductionPrimitives (which works at the HCC level). -/
def PolyCell.subst_dim0_varStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (varPos : Fin srcScope)
    (substituentCell :
      PolyCell profile Generator.gen_var.cellSort 0 tgtScope
        CellBoundary.trivial (.termBase (sigma varPos))) :
    PolyCell profile Generator.gen_var.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.subst sigma
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope))) := by
  -- `subst σ (mkGen gen_var pos childNil) = σ pos` by rfl
  show PolyCell profile Generator.gen_var.cellSort 0 tgtScope
    CellBoundary.trivial (.termBase (sigma varPos))
  exact substituentCell

end FX1Poly.Core
