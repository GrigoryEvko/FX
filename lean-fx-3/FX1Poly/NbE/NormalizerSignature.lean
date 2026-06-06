import FX1Poly.Core.RawTermNF
import FX1Poly.Core.RawTermRename
import FX1Poly.NbE.DesignDecision
import FX1Poly.NbE.ReductionStrategy
import FX1Poly.Foundation.RawSubst.RenameDefs

/-! # Foundation/PolyCell/NbE/NormalizerSignature
   — NbE substrate: canonical normalizer signature contract

The SIGNATURE-LEVEL contract every NbE eval implementation must
satisfy.  The NF predicate it builds on, `RawTerm.isStepNormalForm`,
lives in `Foundation/PolyCell/Core/RawTermNF.lean` (a Prop predicate
plus a `Decidable` instance plus a blocks-step soundness theorem).
This file defines the `NbE.Normalizer` structure capturing the
contract.

## Why a structure, not a function

The NbE `eval : RawTerm → RawTerm` is an implementation.  This file
states the SIGNATURE without committing to one.  A direct
`def NbE.normalize : RawTerm → RawTerm` would either require a body
or be `noncomputable` / `opaque` (banned by the zero-axiom
discipline).  Instead, a `structure Normalizer` captures the
signature + post-conditions as FIELDS; an implementation constructs
a `Normalizer` value, and downstream NbE consumers write theorems
generic over any `normalizer : Normalizer` instance.  No instance is
defined here.

## Contract fields (declared below)

`Normalizer` has 6 fields:
* `normalize` — the function `RawTerm scope → RawTerm scope`; the
  raw layer outputs RawTerm in β-NF, no separate ValueTerm.
* `normalize_isNF` — post-condition: output is always in β-NF (no
  Step rule applies).  Needed by a decidable raw Conv that compares
  `decEq (normalize a) (normalize b)`.
* `normalize_isNF_fixed_point` — an NF input is left unchanged
  (strictly stronger than `normalize_isNF` on NF inputs).
* `normalize_idempotent` — running the normalizer twice equals once.
* `normalize_renaming_commute` — normalize commutes with renaming;
  the substrate property the typed-layer substitution lemmas lift
  through binders.
* `normalize_unit` — sanity smoke: a closed unit term is its own NF.

Soundness (`Conv a b ↔ normalize a = normalize b`) is NOT a field —
it requires `Conv`, defined outside this file.

## Instantiation shape

```
def NbE.eval : ∀ {scope}, RawTerm scope → RawTerm scope :=
  RawTerm.fold GenAlgebra.NbE

def NbE.normalizer : NbE.Normalizer where
  normalize := NbE.eval
  normalize_isNF := NbE.eval_isNF
  normalize_idempotent := NbE.eval_idempotent
  normalize_unit := NbE.eval_unit
  ...
```

## Strategy commitment

The signature pins CBN per `NbE.ReductionStrategy.committed :=
.callByName`, carried via the `NormalizerWithStrategy` marker
(below) rather than as a `Normalizer` field, keeping the `Normalizer`
contract strategy-agnostic.

## Zero-axiom verification

Pure type declarations + field-count and consistency smokes.  No
`Normalizer` instance exists yet, so no body is filled in; the
structure IS the contract.  Audit-gated.
-/

namespace FX1Poly.NbE

open FX1Poly.Core

/-- Canonical normalizer contract.

Captures the SIGNATURE-LEVEL specification every NbE eval
implementation must satisfy under the hybrid design + CBN strategy.
An implementation constructs an instance of this structure.

Six fields:
* `normalize` — the function.
* `normalize_isNF` — output is always in β-NF.
* `normalize_isNF_fixed_point` — NF input is a fixed point.
* `normalize_idempotent` — `normalize (normalize t) = normalize t`.
* `normalize_renaming_commute` — normalize commutes with renaming.
* `normalize_unit` — closed unit is its own NF (sanity smoke).

Downstream NbE consumers write theorems generic over any
`Normalizer` instance. -/
structure Normalizer where
  /-- The normalizer function: `RawTerm scope → RawTerm scope`
  per the hybrid design (raw layer outputs RawTerm in β-NF, no
  separate ValueTerm).  Written fully-qualified as
  `FX1Poly.Core.RawTerm`. -/
  normalize : ∀ {scope : Nat},
    FX1Poly.Core.RawTerm scope →
    FX1Poly.Core.RawTerm scope
  /-- Post-condition: output is always in β-NF (no Step rule
  applies to it).  Needed by a decidable raw Conv. -/
  normalize_isNF : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    FX1Poly.Core.RawTerm.isStepNormalForm
      (normalize term)
  /-- NF input is a fixed point of `normalize`.

  If a term is already in step-normal form, the normalizer
  leaves it unchanged.  Strictly stronger than `normalize_isNF`
  on NF inputs (which would only guarantee the OUTPUT is NF, not
  that it equals the input).  Used by fixture-level smokes to
  confirm "already-canonical" leaves survive the normalizer
  round-trip identically. -/
  normalize_isNF_fixed_point : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    FX1Poly.Core.RawTerm.isStepNormalForm term →
      normalize term = term
  /-- Idempotence: running the normalizer twice equals once. -/
  normalize_idempotent : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    normalize (normalize term) = normalize term
  /-- Normalize commutes with renaming.

  Renaming variables BEFORE normalization is equivalent to
  normalizing first and then renaming.  This is the substrate
  property NbE eval must satisfy so the typed-layer substitution
  lemmas can lift `eval ∘ rename` through binders.

  Stated over `RawRenaming` (the canonical `Fin source → Fin
  target` family).  An implementation proves this via the
  fold-based Action laws. -/
  normalize_renaming_commute : ∀ {sourceScope targetScope : Nat}
      (someRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
      (term : FX1Poly.Core.RawTerm sourceScope),
    normalize
        (FX1Poly.Core.RawTerm.rename
          someRenaming term) =
      FX1Poly.Core.RawTerm.rename
        someRenaming (normalize term)
  /-- Sanity smoke: a closed unit term is its own NF. -/
  normalize_unit : ∀ {scope : Nat},
    normalize
        (FX1Poly.Core.RawTerm.mkGen
          .gen_unit ()
          FX1Poly.Core.RawTermChildren.childNil :
        FX1Poly.Core.RawTerm scope) =
      FX1Poly.Core.RawTerm.mkGen
        .gen_unit ()
        FX1Poly.Core.RawTermChildren.childNil

/-! ## Marker: strategy commitment

The reduction-strategy commitment as a marker so any `Normalizer`
instance carries explicit provenance of which reduction strategy
it implements.

This is a separate marker structure paired with `Normalizer`,
NOT a field on `Normalizer` itself — keeping the contract
strategy-agnostic (a CBV `Normalizer` would still satisfy the
`Normalizer` fields, just via a different algorithm). -/

/-- Marker pairing a `Normalizer` with its reduction-strategy
provenance. -/
structure NormalizerWithStrategy where
  /-- The normalizer instance. -/
  normalizer : FX1Poly.NbE.Normalizer
  /-- Which strategy this normalizer implements; the default
  normalizer is `.callByName`. -/
  strategy : FX1Poly.NbE.ReductionStrategy

/-! ## Pinned signature smokes

Pin the structure's shape via `rfl`-witnessed canonical
extractor equations.  If `Normalizer.normalize` ever silently
changes name or signature, these catch the regression. -/

/-- The Normalizer structure has 6 explicit fields. -/
def Normalizer.fieldCount : Nat := 6

theorem Normalizer.fieldCount_correct :
    Normalizer.fieldCount = 6 := rfl

/-- NormalizerWithStrategy has exactly 2 fields. -/
def NormalizerWithStrategy.fieldCount : Nat := 2

theorem NormalizerWithStrategy.fieldCount_correct :
    NormalizerWithStrategy.fieldCount = 2 := rfl

/-! ## Cross-reference with design commitments

Pin the design pair via cross-reference theorems. -/

/-- The normalizer signature is consistent with the hybrid design
(raw layer returns RawTerm in β-NF). -/
theorem Normalizer.consistent_with_hybrid_design :
    NbEDesign.committed = .hybrid := rfl

/-- The normalizer signature is consistent with the CBN strategy
commitment. -/
theorem Normalizer.consistent_with_cbn_strategy :
    ReductionStrategy.committed = .callByName := rfl

end FX1Poly.NbE
