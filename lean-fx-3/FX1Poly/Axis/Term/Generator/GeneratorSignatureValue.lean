import FX1Poly.Axis.Term.Generator.GeneratorMetadata
import FX1Poly.Axis.Term.Generator.GeneratorTagRoundTrip
import FX1Poly.Axis.Term.Generator.GeneratorCountPin

/-! # GeneratorSignatureValue — SIG-1 [SPIKE]: the signature as a VALUE

The kernel currently reads each generator's structure out of a family of
`Generator → _` dispatch functions (`toNat`, `cellSort`, `arity`,
`binderShifts`, `childSpecs`, `payload`).  SIG-1 spikes the reframe where
that structure is reified into ONE first-order **descriptor** value per
generator, so the whole signature becomes a piece of data the kernel reads
rather than a family of matches — the precondition for SIG-2/SIG-3, where
`SigTerm` is built over an ARBITRARY `Signature` and `StepOver` takes the
signature as a parameter.

## The descriptor

`GeneratorDescriptor` bundles the FIRST-ORDER per-generator metadata:

* `tag` — the `Generator.toNat` head byte (the generator's identity);
* `cellSort` — its output sort;
* `arity` — its child count;
* `binderShifts` — the per-child de Bruijn scope offsets;
* `childSpecs` — the full per-child position table.

`Generator.descriptor` materialises it; `GeneratorDescriptor.toGenerator`
recovers the generator from the `tag` field via the audited
`Generator.fromTag` table.

## What the spike FOUND (the SIG-2 boundary)

`Generator.payload : Generator → Nat → Type` is a scope-indexed DEPENDENT
TYPE family (e.g. `gen_universeCode` carries `LevelExpr × UniverseFlag`),
not first-order data — so it CANNOT be a `GeneratorDescriptor` field
without first reflecting payload types into a code universe.  The
descriptor therefore carries the structural skeleton (identity + sorts +
child shape); payload reflection is the SIG-2 obligation.  This is the
genuine finding of the spike: the signature splits cleanly into a
first-order skeleton (reified here) and a dependent payload layer
(deferred).

## The round-trip ≃

The `Generator ≃ {descriptors}` equivalence is delivered as the two
half-isos (Init-only, no Mathlib `Equiv`):

* `Generator.descriptor_toGenerator_roundTrip` — `toGenerator (descriptor g) = some g`
  (the enum → descriptor → enum left inverse);
* `Generator.descriptor_injective` — distinct generators get distinct
  descriptors (faithfulness).

Plus the signature-value coherence: every tag lands in `[0, generatorCount)`
(`descriptor_tag_lt_generatorCount`), and the descriptor's own child table is
internally consistent (`descriptor_childSpecsLength_eq_arity`,
`descriptor_scopeShifts_eq_binderShifts`) — the descriptor is a faithful
standalone value, not a view that has to reach back into the enum.

## Zero-axiom

The round-trip reuses the audited `Generator.fromTag_toNat` /
`Generator.toNat_injective`; the structural coherences reuse the audited
`childSpecs` lemmas; `descriptor_tag_lt_generatorCount` is the count-pin
`of_decide_eq_true rfl` per constructor.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Core

/-- The first-order skeleton of one generator: identity tag, output sort,
arity, per-child binder shifts, and the full child-position table.  A
self-contained data value — every field is decidable-equal, so the whole
descriptor is.  (The dependent `payload` family is deliberately absent; see
the module docstring.) -/
structure GeneratorDescriptor where
  tag : Nat
  cellSort : CellSort
  arity : Nat
  binderShifts : List Nat
  childSpecs : List ChildSpec
  deriving DecidableEq

/-- Materialise a generator's descriptor: read off its first-order
metadata into one value. -/
def Generator.descriptor (generator : Generator) : GeneratorDescriptor where
  tag := generator.toNat
  cellSort := generator.cellSort
  arity := generator.arity
  binderShifts := generator.binderShifts
  childSpecs := generator.childSpecs

/-- Recover the generator a descriptor describes, from its `tag` field, via
the audited inverse table `Generator.fromTag`.  `none` for an out-of-range
tag. -/
def GeneratorDescriptor.toGenerator (descriptor : GeneratorDescriptor) :
    Option Generator :=
  Generator.fromTag descriptor.tag

/-- **The signature as a VALUE (function form).**  A total descriptor-lookup
keyed by tag: the signature is the data the kernel reads to recover, for any
tag, the generator's skeleton.  `none` exactly off the live tag range. -/
def fxSignatureLookup (tag : Nat) : Option GeneratorDescriptor :=
  (Generator.fromTag tag).map Generator.descriptor

/-- **The signature as a VALUE (materialised list form).**  The full
descriptor table, one entry per live tag `0 … generatorCount-1`, built by
running the lookup over `List.range generatorCount`.  A genuine
`List GeneratorDescriptor` data value — the signature reified as data. -/
def fxSignature : List GeneratorDescriptor :=
  (List.range generatorCount).filterMap fxSignatureLookup

/-! ## The round-trip ≃ -/

/-- **Forward round-trip (enum → descriptor → enum).**  Recovering a
generator from its own descriptor's tag returns it: `toGenerator` is a left
inverse of `descriptor`.  Definitionally the audited `fromTag_toNat`. -/
theorem Generator.descriptor_toGenerator_roundTrip (generator : Generator) :
    (Generator.descriptor generator).toGenerator = some generator :=
  Generator.fromTag_toNat generator

/-- **Faithfulness.**  Distinct generators have distinct descriptors —
because the `tag` field is the injective `toNat`.  Together with the forward
round-trip this is the `Generator ≃ {descriptors}` embedding. -/
theorem Generator.descriptor_injective {firstGenerator secondGenerator : Generator}
    (descriptorsEqual :
      Generator.descriptor firstGenerator = Generator.descriptor secondGenerator) :
    firstGenerator = secondGenerator :=
  Generator.toNat_injective (congrArg GeneratorDescriptor.tag descriptorsEqual)

/-- The function-form signature stores exactly the descriptor at each
generator's own tag: `fxSignatureLookup (toNat g) = some (descriptor g)`. -/
theorem fxSignatureLookup_atTag (generator : Generator) :
    fxSignatureLookup generator.toNat = some (Generator.descriptor generator) := by
  show (Generator.fromTag generator.toNat).map Generator.descriptor
      = some (Generator.descriptor generator)
  rw [Generator.fromTag_toNat]
  rfl

/-! ## Signature-value coherence -/

/-- Every descriptor's tag is a live tag — below the pinned
`generatorCount`.  Ties the reified signature to `GeneratorCountPin`: the
table has no out-of-range identities. -/
theorem Generator.descriptor_tag_lt_generatorCount (generator : Generator) :
    (Generator.descriptor generator).tag < generatorCount := by
  cases generator <;> exact of_decide_eq_true rfl

/-- The descriptor is internally consistent: its `childSpecs` length equals
its declared `arity` (reuses the audited enum-level coherence). -/
theorem Generator.descriptor_childSpecsLength_eq_arity (generator : Generator) :
    (Generator.descriptor generator).childSpecs.length =
      (Generator.descriptor generator).arity :=
  Generator.childSpecs_length_eq_arity generator

/-- The descriptor is internally consistent: the scope shift of each child in
its `childSpecs` agrees with its `binderShifts` field. -/
theorem Generator.descriptor_scopeShifts_eq_binderShifts (generator : Generator) :
    ((Generator.descriptor generator).childSpecs.map ChildSpec.scopeShift) =
      (Generator.descriptor generator).binderShifts :=
  Generator.childSpecs_scopeShifts_eq_binderShifts generator

end FX1Poly.Core
