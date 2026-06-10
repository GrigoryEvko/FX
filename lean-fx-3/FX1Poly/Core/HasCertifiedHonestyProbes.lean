import FX1Poly.Core.HasCertifiedIntros

/-! # Foundation/PolyCell/Core/HasCertifiedHonestyProbes — overadmission probes

## Purpose

The PolyCell substrate provides STRUCTURAL admission, not full
type-theoretic well-typedness.  Describing the substrate as a "type
checker" or as "full Subject Reduction" would be an overclaim.

This file holds **honesty probes**: theorems that DEMONSTRATE the
structural-vs-semantic gap by proving the structural admission of
ill-typed terms.  Each probe is a green theorem proving the
substrate accepts a term that a full type checker would reject.

The probes make the gap audit-visible: a reader inspecting
`HasCertifiedCellDim0` cannot misread it as "well-typed" because
THESE THEOREMS PROVE otherwise.

## The probes

  * `app_unit_unit` — `app unit unit` is structurally admitted
    despite `unit` not having function type.  This is the
    canonical "the substrate is shape-only, not typed" probe.

  * `app_boolTrue_unit` — same point with `boolTrue` as the
    "function".

  * `app_natZero_listNil` — same point with arbitrary
    constructors composed; demonstrates that structural admission
    is closed under nonsensical composition.

## What the probes do NOT mean

They do NOT mean PolyCell is broken — the substrate is doing
exactly what it claims (structural admission).  They mean the
SEMANTIC LAYER (typing judgment) must be layered above the
structural layer before claiming type-theoretic SR.

## The semantic layer

The semantic layer lives in `FX1Poly/Typed`:

  * `TypingContext profile scope` — per-variable types
  * `HasTypeDesc ctx term type` — the typing judgment

The structural preservation arms are a real result over the
structural layer; the SEMANTIC SR theorem
`HasTypeDesc ctx s T → Step s t → HasTypeDesc ctx t T` is a separate,
stronger result for the typed fragment.

These probes establish the baseline that prevents the structural
layer from being misread as the semantic layer.

## Audit-gated

All three probes are gated with `#assert_no_axioms`.  They use
the same `PolyCell.gen` machinery as the legitimate SR arms;
the only difference is the EXAMPLES are ill-typed.
-/

namespace FX1Poly.Core

/-- **Honesty probe: `app(unit, unit)` is structurally admitted.**

This term is ill-typed under any conventional MLTT: `unit` has
type `Unit`, not a function type, so applying it to anything is
a type error.

But under PolyCell's structural admission, both children of
`gen_app` need only have sort `.term` (per
`ChildSpec.termSameScope`).  Both `gen_unit ()` terms satisfy
this, so the application IS structurally admitted.

Demonstrates the structural-vs-semantic gap precisely. -/
theorem HasCertifiedCellDim0.probe_app_unit_unit
    {profile : PolyProfile} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))
        : RawTerm 0) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_app
      (genPayloadEvidence (generator := .gen_app) (scope := 0) ())
      (CertifiedTermSpine.cons
        (PolyCell.gen
          SupportedGenerator.gen_unit
          (genPayloadEvidence (generator := .gen_unit) (scope := 0) ())
          CertifiedTermSpine.nil)
        (CertifiedTermSpine.cons
          (PolyCell.gen
            SupportedGenerator.gen_unit
            (genPayloadEvidence (generator := .gen_unit) (scope := 0) ())
            CertifiedTermSpine.nil)
          CertifiedTermSpine.nil)))

/-- **Honesty probe: `app(boolTrue, unit)` is structurally admitted.**

Variant probe.  `boolTrue` is a value, not a function.  Applying
it to `unit` is ill-typed but structurally admitted. -/
theorem HasCertifiedCellDim0.probe_app_boolTrue_unit
    {profile : PolyProfile} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_boolTrue () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))
        : RawTerm 0) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_app
      (genPayloadEvidence (generator := .gen_app) (scope := 0) ())
      (CertifiedTermSpine.cons
        (PolyCell.gen
          SupportedGenerator.gen_boolTrue
          (genPayloadEvidence (generator := .gen_boolTrue) (scope := 0) ())
          CertifiedTermSpine.nil)
        (CertifiedTermSpine.cons
          (PolyCell.gen
            SupportedGenerator.gen_unit
            (genPayloadEvidence (generator := .gen_unit) (scope := 0) ())
            CertifiedTermSpine.nil)
          CertifiedTermSpine.nil)))

/-- **Honesty probe: nonsense scrutinee in boolElim is structurally admitted.**

`boolElim (λ_.unit) unit unit natZero` is ill-typed: the scrutinee should
be a `Bool`, not a `Nat`.  But structurally, all four children
of `gen_boolElim` (Phase-Z motive shape: motive under one binder + three
same-scope children) have sort `.term`, so the term is admitted.

This shows that even ELIMINATORS, which one might expect to
enforce scrutinee discipline, do NOT do so structurally — the
discipline lives in the semantic layer.  The motive head child (a
throwaway `unit` at scope 1) is admitted by the same uniform spine. -/
theorem HasCertifiedCellDim0.probe_boolElim_natZero_branches
    {profile : PolyProfile} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_unit () .childNil : RawTerm 1)
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
        : RawTerm 0) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_boolElim
      (genPayloadEvidence (generator := .gen_boolElim) (scope := 0) ())
      (CertifiedTermSpine.cons
        (PolyCell.gen
          SupportedGenerator.gen_unit
          (genPayloadEvidence (generator := .gen_unit) (scope := 1) ())
          CertifiedTermSpine.nil)
        (CertifiedTermSpine.cons
          (PolyCell.gen
            SupportedGenerator.gen_unit
            (genPayloadEvidence (generator := .gen_unit) (scope := 0) ())
            CertifiedTermSpine.nil)
          (CertifiedTermSpine.cons
            (PolyCell.gen
              SupportedGenerator.gen_unit
              (genPayloadEvidence (generator := .gen_unit) (scope := 0) ())
              CertifiedTermSpine.nil)
            (CertifiedTermSpine.cons
              (PolyCell.gen
                SupportedGenerator.gen_natZero
                (genPayloadEvidence (generator := .gen_natZero) (scope := 0) ())
                CertifiedTermSpine.nil)
              CertifiedTermSpine.nil)))))

end FX1Poly.Core
