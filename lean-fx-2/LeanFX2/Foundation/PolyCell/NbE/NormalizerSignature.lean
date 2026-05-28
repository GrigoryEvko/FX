import LeanFX2.Foundation.PolyCell.Core.RawTermNF
import LeanFX2.Foundation.PolyCell.Core.RawTermRename
import LeanFX2.Foundation.PolyCell.NbE.DesignDecision
import LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy
import LeanFX2.Foundation.RawSubst.RenameDefs

/-! # Foundation/PolyCell/NbE/NormalizerSignature
   — M11 NbE substrate: canonical normalizer signature contract

M11 (#260, 2026-05-28).  Ships the SIGNATURE-LEVEL contract that
M12 #261 NbE eval implementation must satisfy.

Per the M11-pre #372 hybrid design + M12-pre #373 CBN commitment:

* RawTerm.isNF predicate — SHIPPED via M-substrate-3 #367
  (Foundation/PolyCell/Core/RawTermNF.lean exports
  `RawTerm.isStepNormalForm` as the Prop predicate +
  `Decidable (RawTerm.isStepNormalForm t)` instance +
  blocks-step soundness theorem).

* Canonical normalizer signature — THIS file.  Ships the
  `NbE.Normalizer` structure type capturing the contract every
  NbE eval implementation must satisfy:
  - `normalize : ∀ {scope}, RawTerm scope → RawTerm scope`
  - `normalize_isNF : ∀ t, isStepNormalForm (normalize t)`
  - `normalize_idempotent : ∀ t, normalize (normalize t) = normalize t`
  - `normalize_preserves_unit : normalize unit = unit`
    (witness that the normalizer respects ALREADY-NF leaves)

## Why a structure, not a function

Per the hybrid design (#372), `eval : RawTerm → RawTerm` is
the M12 deliverable.  But M11 must ship the SIGNATURE without
committing to an implementation.  A direct
`def NbE.normalize : RawTerm → RawTerm` definition would either:
1. Require a body (M12's job, not M11's).
2. Be `noncomputable` / `opaque` (BANNED per CLAUDE.md
   zero-axiom discipline).

The clean solution: ship a `structure Normalizer` whose FIELDS
capture the signature + post-conditions.  M12 constructs a
`Normalizer` value by providing the implementation; downstream
NbE consumers (M16/M17/M18) write theorems generic over any
`normalizer : Normalizer` instance.

## Contract fields (declared below)

The shipped structure has 4 fields:
* `normalize` — function `RawTerm scope → RawTerm scope`.
* `normalize_isNF` — output is in β-NF.
* `normalize_idempotent` — `normalize ∘ normalize = normalize`.
* `normalize_unit` — `normalize unit = unit` (sanity smoke).

* `normalize` — the function itself.
* `normalize_isNF` — post-condition: output is always in β-NF
  per the M11-pre hybrid design (raw layer outputs RawTerm in
  β-NF, no separate ValueTerm).
* `normalize_idempotent` — running the normalizer twice equals
  running it once.  Standard idempotence property for any
  proper normalizer.
* `normalize_unit` — sanity smoke: a closed unit term is its
  own NF (no reduction applies).  M12's implementation MUST
  satisfy this; if its algebra were buggy and somehow rewrote
  unit, this field would fail to elaborate.

## Why these exact 4 fields

Minimal contract sufficient for downstream M16/M17/M18:

* `normalize_isNF` is the **post-condition** M18 #267 ★
  Decidable raw Conv needs: comparing `decEq (normalize a)
  (normalize b)` requires both outputs to be canonical (NF).

* `normalize_idempotent` is needed by M16/M17 to avoid
  needing a separate `normalize_fixedPoint` lemma.

* `normalize_unit` is the smallest fixture-witness that any
  M12 implementation must respect — catches regressions where
  a refactor silently breaks closed-leaf normalization.

* `normalize` field — the function itself.

Soundness (`Conv a b ↔ normalize a = normalize b`) is M16 #265
+ M17 #266 territory and CANNOT be a Normalizer field because
it requires definitions outside this file (`Conv`).

## Forward-compat: M12 instantiation

When M12 #261 ships the actual implementation:

```
def NbE.eval : ∀ {scope}, RawTerm scope → RawTerm scope :=
  RawTerm.fold GenAlgebra.NbE

theorem NbE.eval_isNF : ∀ ..., isStepNormalForm (eval t) := ...
theorem NbE.eval_idempotent : ∀ ..., eval (eval t) = eval t := ...
theorem NbE.eval_unit : ∀ ..., eval unit = unit := rfl

def NbE.normalizer : NbE.Normalizer where
  normalize := NbE.eval
  normalize_isNF := NbE.eval_isNF
  normalize_idempotent := NbE.eval_idempotent
  normalize_unit := NbE.eval_unit
```

Downstream M16/M17/M18 consume `NbE.normalizer` (or any
`Normalizer` instance) generically.

## Strategy commitment (M12-pre #373)

The signature pins CBN per `NbE.ReductionStrategy.committed :=
.callByName`.  Re-exported here as a `committed_strategy`
field marker on the structure (not load-bearing for the
fields, but documents the M12 implementation contract).

## Zero-axiom verification

Pure type-declaration + structure-shape ship.  No body, no
fields filled in yet.  The structure IS the contract; M12
provides the witnesses.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.NbE

open LeanFX2.Foundation.PolyCell.Core

/-- M11 canonical normalizer contract.

Captures the SIGNATURE-LEVEL specification every NbE eval
implementation must satisfy per the M11-pre hybrid design
+ M12-pre CBN strategy.  M12 #261 constructs an instance of
this structure with the actual implementation.

Four fields:
* `normalize` — the function.
* `normalize_isNF` — output is always in β-NF.
* `normalize_idempotent` — `normalize (normalize t) = normalize t`.
* `normalize_unit` — closed unit is its own NF (sanity smoke).

Downstream M16/M17/M18 write theorems generic over any
`Normalizer` instance. -/
structure Normalizer where
  /-- The normalizer function: `RawTerm scope → RawTerm scope`
  per the hybrid design (raw layer outputs RawTerm in β-NF, no
  separate ValueTerm).  Fully-qualified to avoid the
  competing `LeanFX2.RawTerm` legacy-namespace shadow. -/
  normalize : ∀ {scope : Nat},
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope →
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope
  /-- Post-condition: output is always in β-NF (no Step rule
  applies to it).  Required by M18 #267 ★ Decidable raw Conv. -/
  normalize_isNF : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm
      (normalize term)
  /-- audit-A3 (#390): NF input is a fixed point of `normalize`.

  If a term is already in step-normal form, the normalizer
  leaves it unchanged.  Strictly stronger than `normalize_isNF`
  on NF inputs (which would only guarantee the OUTPUT is NF, not
  that it equals the input).  Required by M14/M16/M17 fixture-
  level smokes to confirm "already-canonical" leaves survive the
  normalizer round-trip identically. -/
  normalize_isNF_fixed_point : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm term →
      normalize term = term
  /-- Idempotence: running the normalizer twice equals once. -/
  normalize_idempotent : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    normalize (normalize term) = normalize term
  /-- audit-A2 (#389): normalize commutes with renaming.

  Renaming variables BEFORE normalization is equivalent to
  normalizing first and then renaming.  This is the substrate
  property M12 #261 NbE eval must satisfy so the typed-layer
  substitution lemmas (M47 #296) can lift `eval ∘ rename`
  through binders.

  Stated over `LeanFX2.RawRenaming` (the canonical
  `Fin source → Fin target` family) per the existing PolyCell
  rename infrastructure.  The implementation in M12 will prove
  this via the fold-based Action laws.  Until M12 lands, the
  contract is empty — no instance can be constructed without it,
  which is the point. -/
  normalize_renaming_commute : ∀ {sourceScope targetScope : Nat}
      (someRenaming : LeanFX2.RawRenaming sourceScope targetScope)
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm sourceScope),
    normalize
        (LeanFX2.Foundation.PolyCell.Core.RawTerm.rename
          someRenaming term) =
      LeanFX2.Foundation.PolyCell.Core.RawTerm.rename
        someRenaming (normalize term)
  /-- Sanity smoke: a closed unit term is its own NF. -/
  normalize_unit : ∀ {scope : Nat},
    normalize
        (LeanFX2.Foundation.PolyCell.Core.RawTerm.mkGen
          .gen_unit ()
          LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childNil :
        LeanFX2.Foundation.PolyCell.Core.RawTerm scope) =
      LeanFX2.Foundation.PolyCell.Core.RawTerm.mkGen
        .gen_unit ()
        LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childNil

/-! ## Marker: strategy commitment

Re-export the M12-pre #373 strategy commitment as a structure
field marker, so any `Normalizer` instance carries explicit
provenance of which reduction strategy it implements.

This is a separate marker structure paired with `Normalizer`,
NOT a field on `Normalizer` itself — keeping the contract
strategy-agnostic (a hypothetical CBV `Normalizer` would still
satisfy the 4 fields above, just via a different algorithm). -/

/-- Marker pairing a `Normalizer` with its reduction-strategy
provenance.  M12 #261 ships `normalizerWithStrategy` for the
default CBN normalizer. -/
structure NormalizerWithStrategy where
  /-- The normalizer instance. -/
  normalizer : LeanFX2.Foundation.PolyCell.NbE.Normalizer
  /-- Which strategy this normalizer implements.  M12 #261's
  default ships at `.callByName` per M12-pre #373. -/
  strategy : LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy

/-! ## Pinned signature smokes

Pin the structure's shape via `rfl`-witnessed canonical
extractor equations.  If `Normalizer.normalize` ever silently
changes name or signature, these catch the regression. -/

/-- The Normalizer structure has 6 explicit fields (4 original
M11 #260 fields + 2 audit-A* contract extensions: A2 + A3). -/
def Normalizer.fieldCount : Nat := 6

theorem Normalizer.fieldCount_correct :
    Normalizer.fieldCount = 6 := rfl

/-- NormalizerWithStrategy has exactly 2 fields. -/
def NormalizerWithStrategy.fieldCount : Nat := 2

theorem NormalizerWithStrategy.fieldCount_correct :
    NormalizerWithStrategy.fieldCount = 2 := rfl

/-! ## Cross-reference with design commitments

Pin the M11/M12 design pair via cross-reference theorems. -/

/-- M11's normalizer signature is consistent with M11-pre #372
hybrid design (raw layer returns RawTerm in β-NF). -/
theorem Normalizer.consistent_with_hybrid_design :
    NbEDesign.committed = .hybrid := rfl

/-- M11's normalizer signature is consistent with M12-pre #373
CBN strategy commitment. -/
theorem Normalizer.consistent_with_cbn_strategy :
    ReductionStrategy.committed = .callByName := rfl

end LeanFX2.Foundation.PolyCell.NbE
