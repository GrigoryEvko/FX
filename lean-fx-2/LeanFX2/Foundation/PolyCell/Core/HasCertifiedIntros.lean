import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell

/-! # Foundation/PolyCell/Core/HasCertifiedIntros — nullary-generator intros

V2-L3.1 phase D step 13 (2026-05-27).  Ships **smart constructors**
for `HasCertifiedCellDim0` over nullary (zero-children) generators.

## What this gives us

For every Generator `g` with `g.childSpecs = []` and
`g.payload scope = Unit`, `HasCertifiedCellDim0 (.mkGen g () .childNil)`
is unconditionally provable: just instantiate `PolyCell.gen` with
the global `SupportedGenerator.g` admission witness, the default
`()` payload evidence, and the empty `CertifiedTermSpine.nil`
spine.

This file ships those intros as 1-line `theorem`s, one per
nullary generator currently used by SR's iota arms (extracted
from `Step.lean`'s constructor list).

## Why now

The existing compound-iota SR arms (`iotaEitherMatchInl` etc.)
build target cells via explicit `PolyCell.gen
SupportedGenerator.gen_X (genPayloadEvidence ...) (.cons ... .nil)`
chains.  Smart constructors collapse the "produce a certified
leaf cell" idiom to a single intro per leaf, making future SR
work (especially `beta`'s subst-preservation chain) more
readable.

These also provide load-bearing infrastructure for the eventual
cell-level `HasCertifiedCellDim0.preservedByRename` /
`preservedBySubst` mutual block (the remaining SR-beta blocker):
the inductive base cases over leaves are exactly these intros.

## Zero-axiom verification

Each intro closes by direct `PolyCell.gen` construction.  No
tactics needed; no propext risk; no mutual recursion.
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-! ## Section 1 — Variable intro

The only `gen_var` ctor has a `Fin scope` payload (the variable
index).  Trivially certified at any scope. -/

/-- **Intro: every variable is certified.**

A `.mkGen .gen_var varIndex .childNil` is unconditionally a
certified dim-0 term cell at sort `.term`. -/
theorem HasCertifiedCellDim0.var
    {profile : PolyProfile} {scope : Nat} (varIndex : Fin scope) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_var varIndex .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_var
      (genPayloadEvidence (generator := .gen_var)
                           (scope := scope) varIndex)
      CertifiedTermSpine.nil)

/-! ## Section 2 — Nullary value intros

The unit / bool / nat / list / option value-formers all have
`Unit` payload and empty children spine.  Trivially certified. -/

/-- **Intro: the unit value is certified.** -/
theorem HasCertifiedCellDim0.unit
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_unit () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_unit
      (genPayloadEvidence (generator := .gen_unit)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

/-- **Intro: `boolTrue` is certified.** -/
theorem HasCertifiedCellDim0.boolTrue
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_boolTrue () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_boolTrue
      (genPayloadEvidence (generator := .gen_boolTrue)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

/-- **Intro: `boolFalse` is certified.** -/
theorem HasCertifiedCellDim0.boolFalse
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_boolFalse () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_boolFalse
      (genPayloadEvidence (generator := .gen_boolFalse)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

/-- **Intro: `natZero` is certified.** -/
theorem HasCertifiedCellDim0.natZero
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_natZero () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natZero
      (genPayloadEvidence (generator := .gen_natZero)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

/-- **Intro: `listNil` is certified.** -/
theorem HasCertifiedCellDim0.listNil
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_listNil () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_listNil
      (genPayloadEvidence (generator := .gen_listNil)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

/-- **Intro: `optionNone` is certified.** -/
theorem HasCertifiedCellDim0.optionNone
    {profile : PolyProfile} {scope : Nat} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_optionNone () .childNil : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_optionNone
      (genPayloadEvidence (generator := .gen_optionNone)
                           (scope := scope) ())
      CertifiedTermSpine.nil)

end LeanFX2.Foundation.PolyCell.Core
