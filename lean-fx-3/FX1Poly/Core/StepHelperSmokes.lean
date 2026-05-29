import FX1Poly.Core.StepHCCWrappers
import FX1Poly.Core.SpineConsStep

/-! # Foundation/PolyCell/Core/StepHelperSmokes
   — composition smokes for the cell-step + spine cons-step + HCC wrappers

V2-L3.1 phase D step 36 (2026-05-27).  Composition validation for the
six iterations of step-helper infrastructure shipped today.  Each
smoke demonstrates the helpers actually compose on concrete inputs,
acting as regression gates AND providing template proofs for arm-by-
arm SR-cong work when the mutual block lands.

## What this ships

Seven concrete fixtures exercising the cell-step renamers on the
seven nullary leaves (one var arm + six closed leaves), built via
the new infrastructure rather than via the existing
`_preservedByRename` per-generator theorems.

The smokes serve as:

  1. **Regression gates** — if the step helpers' types drift, these
     smokes break.
  2. **Template proofs** — show callers (and future warriors) how
     to invoke the step helpers concretely.
  3. **Composition validation** — empirically verify that the
     cell-step + spine cons-step + HCC wrappers' signatures align
     with usage.

## Why nullary only

The seven nullary smokes are CONCRETE (no children → no spine
recursion needed → no mutual block needed).  Compound generators
(app, pair, lam, etc.) require either:
  * the eventual mutual block's spine recursion, OR
  * manual spine construction via consStep + cell-step helpers.

The latter is shippable today but is per-arity; we defer it to
the next iteration when we batch the SR-cong arm-by-arm work.

## Zero-axiom verification

Each smoke composes existing zero-axiom helpers.  Each closes by a
single invocation of the appropriate step helper.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Cell-level (Type-valued) smokes via step renamers -/

/-- **Smoke: rename `unit` via `rename_dim0_nonVarStep`.**

The simplest non-var case: `gen_unit` has no children, so the
"renamed spine" hypothesis is just `.nilStep` (= `.nil`). -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_unit.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_unit) rho (by decide)
    () .childNil SupportedGenerator.gen_unit .nil

/-- **Smoke: rename `boolTrue` via `rename_dim0_nonVarStep`.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_boolTrue.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_boolTrue () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_boolTrue) rho (by decide)
    () .childNil SupportedGenerator.gen_boolTrue .nil

/-- **Smoke: rename `boolFalse` via `rename_dim0_nonVarStep`.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_boolFalse.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_boolFalse () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_boolFalse) rho (by decide)
    () .childNil SupportedGenerator.gen_boolFalse .nil

/-- **Smoke: rename `natZero` via `rename_dim0_nonVarStep`.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_natZero.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_natZero () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_natZero) rho (by decide)
    () .childNil SupportedGenerator.gen_natZero .nil

/-- **Smoke: rename `listNil` via `rename_dim0_nonVarStep`.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_listNil.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_listNil () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_listNil) rho (by decide)
    () .childNil SupportedGenerator.gen_listNil .nil

/-- **Smoke: rename `optionNone` via `rename_dim0_nonVarStep`.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    PolyCell profile Generator.gen_optionNone.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_optionNone () .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_nonVarStep (generator := .gen_optionNone) rho (by decide)
    () .childNil SupportedGenerator.gen_optionNone .nil

/-- **Smoke: rename `var` via `rename_dim0_varStep`.**

Var is the only generator using the var-step variant.  No children,
no admission witness needed at the call site (varStep handles it). -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) (varPos : Fin sourceScope) :
    PolyCell profile Generator.gen_var.cellSort 0 tgtScope
      CellBoundary.trivial
      (.termBase (RawTerm.rename rho
        (.mkGen .gen_var varPos .childNil : RawTerm sourceScope))) :=
  PolyCell.rename_dim0_varStep (profile := profile) rho varPos

/-! ## Section 2 — HCC-level (Prop-valued) smokes via HCC wrappers -/

/-- **Smoke: HCC.rename_nonVarStep on unit produces unit-HCC at target.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) :=
  HasCertifiedCellDim0.rename_nonVarStep (generator := .gen_unit) rho (by decide)
    () .childNil SupportedGenerator.gen_unit .nil

/-- **Smoke: HCC.rename_varStep on var produces var-HCC at target.** -/
example {profile : PolyProfile} {sourceScope tgtScope : Nat}
    (rho : RawRenaming sourceScope tgtScope) (varPos : Fin sourceScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rho
        (.mkGen .gen_var varPos .childNil : RawTerm sourceScope)) :=
  HasCertifiedCellDim0.rename_varStep (profile := profile) rho varPos

/-! ## Section 3 — Spine cons-step composition smoke

Demonstrates `consStep_dim0Trivial` + `nilStep` build a 1-element
spine over a single head cell.  Uses unit as the head's underlying
raw to keep the fixture concrete. -/

/-- **Smoke: build a 1-element spine over a unit cell using
`consStep_dim0Trivial` + `.nilStep`.**

The spine has one head spec `.termSameScope` (dim 0, scope shift 0),
no rest specs.  Validates that the cons step accepts the dim-0
hypothesis and produces a typed spine. -/
example {profile : PolyProfile} {scope : Nat}
    (headCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (.mkGen .gen_unit () .childNil : RawTerm scope))) :
    CertifiedTermSpine profile [ChildSpec.termSameScope] scope [0]
      (.childCons (.mkGen .gen_unit () .childNil) .childNil) :=
  CertifiedTermSpine.consStep_dim0Trivial (rfl) headCell
    CertifiedTermSpine.nilStep

end FX1Poly.Core
