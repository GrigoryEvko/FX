import LeanFX2.Foundation.PolyCell.Core.StructuralInductionPrimitives
import LeanFX2.Foundation.PolyCell.Core.GeneratorChildSpecsDim0

/-! # Foundation/PolyCell/Core/CellNonVarStepRenamer
   — abstract non-recursive cell renamer step (one half of the eventual mutual block)

V2-L3.1 phase D step 32 (2026-05-27).  Ships the **cell-side
inductive step** of the eventual structural-induction mutual block
for rename preservation — packaged as a NON-RECURSIVE theorem that
takes the recursively-renamed spine as a HYPOTHESIS.

## What this ships

Two Type-valued definitions closing the cell side of the mutual
block, factored out so the spine-side and termination-proof
obligations can be addressed independently.  `def` (not `theorem`)
because `PolyCell ...` returns `Type`, not `Prop`:

  * `PolyCell.rename_dim0_nonVarStep` — for a non-var generator
    `generator ≠ .gen_var`, given a pre-renamed spine, rebuild the
    parent cell at the target scope.  This is the BODY of the
    eventual `rename_dim0`'s non-var arm.

  * `PolyCell.rename_dim0_varStep` — for the var case, no spine
    needed; renames the var-index via `rho` and rebuilds.  Sibling
    of `subst_var_certify` (StructuralInductionPrimitives.lean §3).

## Why this matters

The full mutual block requires (1) well-founded termination over an
indexed inductive (structural recursion fails because indices aren't
variables) and (2) a dependent cast through the existential
`headBoundary` on `CertifiedTermSpine.cons`.  Both are deep
engineering problems requiring focused work.

The factored helpers shipped here are NOT blocked by either
problem — they take the recursively-renamed children as input.
When the mutual block lands, its non-var arm becomes a one-line
invocation of `rename_dim0_nonVarStep` with the recursive spine
call supplied as argument.

## Pattern alignment

Sibling of the existing `StructuralInductionWrapper.lean` decls,
which take the FULL cell renamer as hypothesis (HCC-level Prop
wrappers).  This file is at the cell level (Type-valued) and takes
the spine renamer as hypothesis — finer-grained.

## Zero-axiom verification

Both helpers compose existing zero-axiom primitives:
`rename_nonVar_reduces` (StructuralInductionPrimitives), the
PolyCell.gen constructor, and the `Generator.childSpecs` value.
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- **Cell-level rename step for the non-var case.**

Given:
  * a non-var generator `generator ≠ .gen_var`,
  * its payload and (original) children at source scope,
  * the SupportedGenerator admission witness,
  * the original spine over the source-scope children,
  * the SPINE RENAMER's output (the renamed spine at target scope),

produces the renamed cell at the target scope with dim 0 and
trivial boundary.

This is the body of the future
`PolyCell.rename_dim0`'s non-var arm, abstracted from the
recursion: callers (eventually, the mutual block) supply the
renamed spine via `renamedSpine`. -/
def PolyCell.rename_dim0_nonVarStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    {generator : Generator}
    (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload srcScope)
    (children : RawTermChildren generator.binderShifts srcScope)
    (admission : SupportedGenerator generator)
    (renamedSpine :
      CertifiedTermSpine profile generator.childSpecs tgtScope
        generator.binderShifts
        (foldChildren GenAlgebra.canonical rho children)) :
    PolyCell profile generator.cellSort 0 tgtScope CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen generator payload children : RawTerm srcScope))) := by
  rw [RawTerm.rename_nonVar_reduces rho hNotVar payload children]
  exact PolyCell.gen admission
    (genPayloadEvidence (generator := generator) (scope := tgtScope) _)
    renamedSpine

/-- **Cell-level rename step for the var case.**

For `generator = .gen_var`, the rename produces a fresh var cell
at the target scope using `rho varPos` as the renamed index.  No
spine needed — var has empty children.

Sibling of `HasCertifiedCellDim0.rename_var_certify` from
`StructuralInductionPrimitives.lean`, at the cell level (not HCC)
to match the non-var sibling's signature. -/
def PolyCell.rename_dim0_varStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    (varPos : Fin srcScope) :
    PolyCell profile Generator.gen_var.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope))) := by
  -- `rename ρ (mkGen gen_var pos childNil) = mkGen gen_var (ρ pos) childNil` by rfl
  show PolyCell profile Generator.gen_var.cellSort 0 tgtScope
    CellBoundary.trivial
    (.termBase (.mkGen .gen_var (rho varPos) .childNil))
  exact PolyCell.gen
    SupportedGenerator.gen_var
    (genPayloadEvidence (generator := .gen_var) (scope := tgtScope) (rho varPos))
    .nil

end LeanFX2.Foundation.PolyCell.Core
