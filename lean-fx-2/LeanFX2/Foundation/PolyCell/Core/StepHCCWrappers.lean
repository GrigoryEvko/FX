import LeanFX2.Foundation.PolyCell.Core.CellNonVarStepRenamer
import LeanFX2.Foundation.PolyCell.Core.CellNonVarStepSubstituter

/-! # Foundation/PolyCell/Core/StepHCCWrappers
   — Prop-output HCC wrappers around the cell-step helpers

V2-L3.1 phase D step 35 (2026-05-27).  Ships HCC (`HasCertifiedCellDim0`,
Prop-valued) wrappers around the Type-valued cell-step helpers from
`CellNonVarStepRenamer.lean` (step 32) and
`CellNonVarStepSubstituter.lean` (step 33).

## What this ships

Four Prop-valued theorems closing the HCC-level cell side of the
eventual mutual block — same recipe as the cell-step defs, but
wrapping the Type-valued cell with `HasCertifiedCellDim0.intro` to
land in Prop:

  * `HasCertifiedCellDim0.rename_nonVarStep` — Prop wrapper of
    `PolyCell.rename_dim0_nonVarStep`.
  * `HasCertifiedCellDim0.rename_varStep` — Prop wrapper of
    `PolyCell.rename_dim0_varStep`.
  * `HasCertifiedCellDim0.subst_nonVarStep` — Prop wrapper of
    `PolyCell.subst_dim0_nonVarStep`.
  * `HasCertifiedCellDim0.subst_varStep` — Prop wrapper of
    `PolyCell.subst_dim0_varStep`.

## Why both APIs exist

The Type-valued cell-step helpers expose the produced cell at a
known sort (used internally by the eventual mutual block).  The
HCC wrappers package the sort existentially, giving the public-
facing Prop-level API (used by SR-cong / SR-beta umbrellas).

Both share the same proof pattern: invoke the matching cell-step
def, then `.intro sort cellResult` to package into HCC.

## Zero-axiom verification

Each wrapper is a 1-line composition `.intro _ (PolyCell.X _)`.
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- **HCC-level: rename preservation for the non-var case via the
spine renamer hypothesis.**

Wraps `PolyCell.rename_dim0_nonVarStep` with `HCC.intro`. -/
theorem HasCertifiedCellDim0.rename_nonVarStep
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
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho
        (.mkGen generator payload children : RawTerm srcScope)) :=
  .intro generator.cellSort
    (PolyCell.rename_dim0_nonVarStep rho hNotVar payload children
      admission renamedSpine)

/-- **HCC-level: rename preservation for the var case.**

Wraps `PolyCell.rename_dim0_varStep` with `HCC.intro`.  Sibling of
`rename_var_certify` (StructuralInductionPrimitives §3) — same
output, different proof path via the cell-step helper. -/
theorem HasCertifiedCellDim0.rename_varStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope)
    (varPos : Fin srcScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope)) :=
  .intro Generator.gen_var.cellSort
    (PolyCell.rename_dim0_varStep rho varPos)

/-- **HCC-level: subst preservation for the non-var case via the
spine substituter hypothesis.**

Wraps `PolyCell.subst_dim0_nonVarStep` with `HCC.intro`. -/
theorem HasCertifiedCellDim0.subst_nonVarStep
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
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst sigma
        (.mkGen generator payload children : RawTerm srcScope)) :=
  .intro generator.cellSort
    (PolyCell.subst_dim0_nonVarStep sigma hNotVar payload children
      admission substitutedSpine)

/-- **HCC-level: subst preservation for the var case via the
substituent's cell hypothesis.**

Wraps `PolyCell.subst_dim0_varStep` with `HCC.intro`.  The substituent
cell hypothesis here mirrors `subst_var_certify`'s "every σ output is
certified" hypothesis at the cell level rather than HCC level. -/
theorem HasCertifiedCellDim0.subst_varStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (varPos : Fin srcScope)
    (substituentCell :
      PolyCell profile Generator.gen_var.cellSort 0 tgtScope
        CellBoundary.trivial (.termBase (sigma varPos))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst sigma
        (.mkGen .gen_var varPos .childNil : RawTerm srcScope)) :=
  .intro Generator.gen_var.cellSort
    (PolyCell.subst_dim0_varStep sigma varPos substituentCell)

end LeanFX2.Foundation.PolyCell.Core
