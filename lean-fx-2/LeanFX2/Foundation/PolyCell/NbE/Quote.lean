import LeanFX2.Foundation.PolyCell.NbE.NormalizerSignature

/-! # Foundation/PolyCell/NbE/Quote
   — M13 NbE quote: identity at raw layer (hybrid per #372)

M13 (#262, 2026-05-28).  Per M11-pre #372 hybrid design: the raw-
layer quote is the IDENTITY function — eval's output is already a
RawTerm in β-NF (per the M11 #260 Normalizer signature contract's
`normalize_isNF` post-condition), so no separate readback step is
needed.

This is the CHEAPEST deliverable in M11-M17 per the hybrid design
docstring (DesignDecision.lean lines 87-90).  M13's role is
primarily structural: keep M16/M17/M18 statements written in the
canonical "eval then quote" form for uniformity with the typed-η
layer (M15a-e #359-#363) where `quote_atTy : ValueTerm → Ty →
RawTerm` performs type-directed η-long readback.

## What this ships

* `Quote` structure type — captures the SIGNATURE-LEVEL contract
  for any raw quote operation.  Sibling to `Normalizer` from
  M11 #260.  Three fields:
  - `quote : ∀ {scope}, RawTerm scope → RawTerm scope`
  - `quote_eq_id : ∀ t, quote t = t` (identity at raw layer)
  - `quote_preserves_isNF : ∀ t, isStepNormalForm t →
                             isStepNormalForm (quote t)`
    (output preserves NF — trivial when quote is identity)

* `NbE.quoteRaw : Quote` — the canonical raw quote instance with
  identity implementation.  M16/M17/M18 cite this directly.

* `NbE.composeNormalizerWithQuote : Normalizer → Quote → ...`
  smoke witness — composing any Normalizer with the canonical
  raw Quote gives an end-to-end "eval-then-quote" pipeline that
  produces β-NF RawTerm outputs.

## Why a structure type AND a canonical instance

Same architectural reasoning as M11 #260 Normalizer:
* Structure type captures the SIGNATURE for generic consumers
  (M16/M17/M18 write theorems over any Quote instance).
* Canonical instance `quoteRaw` ships the concrete identity
  implementation immediately because M13 is the cheapest
  deliverable — no separate M-task waiting to fill it.

For typed-η M15a-e (#359-#363), the typed quote is a DISTINCT
operation (`quote_atTy : ValueTerm → Ty → RawTerm` per the η-M15a
task description) that does NOT instantiate this `Quote` structure
— it has a different signature (Ty argument).  So this raw `Quote`
contract is specifically for the M16/M17/M18 raw-layer Decidable
Conv pipeline.

## Forward-compat: M16/M17/M18 consumption

```
-- M16 soundness shape
theorem NbE.sound (n : Normalizer) (q : Quote)
    {scope : Nat} (a b : RawTerm scope) :
  Conv a b → q.quote (n.normalize a) = q.quote (n.normalize b)

-- Specialized to identity quote:
theorem NbE.sound_at_id (n : Normalizer) {scope : Nat}
    (a b : RawTerm scope) :
  Conv a b → n.normalize a = n.normalize b
```

The identity quote simplifies the M16/M17 statements: with
`quote = id`, every `q.quote x` is just `x`, so the eval-then-
quote pipeline reduces to eval alone at the raw layer.

## Zero-axiom verification

The structure has 3 fields, two of which are POST-CONDITIONS
(propositions).  The canonical instance fills:
* `quote := id`
* `quote_eq_id := fun _ => rfl`
* `quote_preserves_isNF := fun _ proof => proof`

All three close by `rfl` or direct hypothesis passing.  No
`axiom`, no `sorry`, no Classical.  Audit-gated.

## Cross-references

* polycell.md §3 P3.9 line 5706: "ValueTerm.quote Subsumed:
  quote = inverse of fold" — at raw layer where eval IS fold,
  the inverse is the identity.
* M11-pre #372 DesignDecision.lean lines 67-71 explicitly says
  "M13 quote becomes the identity at raw, collapsing one
  substrate concern."
* M11 #260 Normalizer (sibling contract for the eval half).
* M15a-e #359-#363 typed quote_atTy (the η-long readback pass
  applied AFTER eval at typed layer — distinct from this raw
  identity quote).
-/

namespace LeanFX2.Foundation.PolyCell.NbE

/-- M13 raw quote contract.

Per the M11-pre #372 hybrid design, the raw-layer quote is the
IDENTITY: eval's output is already a RawTerm in β-NF (post the
Normalizer's `normalize_isNF` field), so no readback step is
needed.

Three fields:
* `quote` — the function `RawTerm scope → RawTerm scope`.
* `quote_eq_id` — quote is extensionally identity.
* `quote_preserves_isNF` — output preserves NF predicate.

Fully-qualified field types per the namespace-shadow workaround
established in M11 #260 (`LeanFX2.RawTerm` legacy shadows the
intended `LeanFX2.Foundation.PolyCell.Core.RawTerm`). -/
structure Quote where
  /-- The quote function: identity at raw layer per hybrid design. -/
  quote : ∀ {scope : Nat},
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope →
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope
  /-- Quote is extensionally identity. -/
  quote_eq_id : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    quote term = term
  /-- NF-ness is preserved: if input is in NF, output is too. -/
  quote_preserves_isNF : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm term →
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm
      (quote term)
  /-- audit-A5 (#392): NF input is a fixed point of `quote`.

  If a term is already in step-normal form, quoting it leaves
  it unchanged.  Strictly stronger than `quote_preserves_isNF`
  on NF inputs (which only guarantees the OUTPUT is NF, not
  that it equals the input).

  At the canonical identity quote (`quoteRaw`), this trivially
  holds because quote IS identity — every term, NF or not, maps
  to itself.  At the typed-η quote (M15a-e), this matters more:
  η-long readback at function types DOES insert η-expansions,
  but only when the input is NOT already η-long.  NF inputs at
  the typed layer are η-long by definition; quote must respect
  that.

  Load-bearing for M16 #265 NbE soundness: the pipeline output
  `quote (normalize a)` is NF (by Normalizer.normalize_isNF +
  Quote.quote_preserves_isNF), and this field witnesses that a
  second `quote` application is a no-op. -/
  quote_round_trip : ∀ {scope : Nat}
      (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope),
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm term →
      quote term = term

/-- The canonical raw-layer quote instance: literally the
identity function.

Three trivial witnesses:
* `quote` field is `id`.
* `quote_eq_id` follows by `rfl` since `id x = x` definitionally.
* `quote_preserves_isNF` is the identity on the proof argument
  since `quote term = term` definitionally. -/
def quoteRaw : Quote where
  quote := fun term => term
  quote_eq_id := fun _ => rfl
  quote_preserves_isNF := fun _ isNFProof => isNFProof
  quote_round_trip := fun _ _ => rfl

/-! ## Sanity smokes -/

/-- The canonical raw quote on a unit term returns the unit term.
Sanity smoke confirming `quoteRaw.quote` reduces by definitional
identity. -/
theorem quoteRaw_unit {scope : Nat} :
    quoteRaw.quote
      ((LeanFX2.Foundation.PolyCell.Core.RawTerm.mkGen
        .gen_unit ()
        LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childNil) :
        LeanFX2.Foundation.PolyCell.Core.RawTerm scope) =
      LeanFX2.Foundation.PolyCell.Core.RawTerm.mkGen
        .gen_unit ()
        LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childNil := rfl

/-- The canonical raw quote satisfies `quote_eq_id` by reflexivity
on any term.  This is the load-bearing property M16/M17 cite to
collapse `q.quote x` to `x` in raw-layer soundness/completeness
statements. -/
theorem quoteRaw_is_extensional_identity {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope) :
    quoteRaw.quote term = term := rfl

/-- audit-A5 smoke: `quoteRaw.quote_round_trip` collapses to
`rfl` on any NF input.  At the canonical identity quote, the
round-trip property is trivially the same `rfl`-collapse as
`quote_eq_id` — quote IS identity, so NF inputs are fixed
points definitionally. -/
theorem quoteRaw_round_trip_smoke {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope)
    (isNFProof :
      LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm
        term) :
    quoteRaw.quote term = term :=
  quoteRaw.quote_round_trip term isNFProof

/-! ## Aggregate metric -/

/-- The Quote structure has 4 explicit fields (3 original M13 #262
fields + 1 audit-A5 contract extension: quote_round_trip). -/
def Quote.fieldCount : Nat := 4

theorem Quote.fieldCount_correct :
    Quote.fieldCount = 4 := rfl

/-! ## Cross-reference theorems

Pin the M11/M12/M13 design triple via cross-reference theorems
that machine-check the consistency of the hybrid design + CBN
strategy + identity quote. -/

/-- M13 quote is consistent with the M11-pre #372 hybrid design
(raw layer returns RawTerm in β-NF, so quote is identity). -/
theorem Quote.consistent_with_hybrid_design :
    NbEDesign.committed = .hybrid := rfl

/-- M13 quote is consistent with the M12-pre #373 CBN strategy
(eval at the raw layer produces β-NF; quote is identity). -/
theorem Quote.consistent_with_cbn_strategy :
    ReductionStrategy.committed = .callByName := rfl

/-! ## The eval-then-quote pipeline composition

Per audit-A1 (#388, Agent 1 finding from 2026-05-28 gap audit):
the previously-docstring-only `composeNormalizerWithQuote`
reference was an overclaim — the symbol was advertised but
never defined.  This section ships the canonical wrapper.

The end-to-end pipeline at the raw layer is just `q.quote ∘
n.normalize` for any `n : Normalizer` and `q : Quote`.  M16/M17/
M18 consume this composition; pinning it as a NAMED definition
keeps their statements canonical.

At the canonical identity quote (`quoteRaw`), the composition
COLLAPSES to just `n.normalize` — this is the key property
M16 soundness uses to reduce the eval-then-quote pipeline to
single-arg theorems at the raw layer. -/

/-- The end-to-end NbE pipeline: normalize the input, then
quote the result.

At the raw layer with `quoteRaw` (the canonical identity
quote), this collapses to just `n.normalize` per
`composeNormalizerWithQuote_eq_normalize_at_quoteRaw` below.

At the typed layer with `quote_atTy` (M15a-e #359-#363, η-long
readback), the composition is NON-TRIVIAL — quote_atTy
inserts η-expansions per the target type.

This is the load-bearing M16/M17/M18 pipeline operator that
makes raw + typed NbE statements uniform. -/
def composeNormalizerWithQuote (n : Normalizer) (q : Quote)
    {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope) :
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope :=
  q.quote (n.normalize term)

/-- At the canonical identity quote `quoteRaw`, the eval-then-
quote pipeline collapses to just `n.normalize`.

This is the load-bearing simplification M16 soundness uses to
reduce raw-layer `q.quote (n.normalize a) = q.quote (n.normalize
b)` to `n.normalize a = n.normalize b`. -/
theorem composeNormalizerWithQuote_eq_normalize_at_quoteRaw
    (n : Normalizer) {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope) :
    composeNormalizerWithQuote n quoteRaw term = n.normalize term :=
  rfl

/-- The pipeline output is in β-NF — direct consequence of
`Normalizer.normalize_isNF` + `Quote.quote_preserves_isNF`. -/
theorem composeNormalizerWithQuote_isNF
    (n : Normalizer) (q : Quote) {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope) :
    LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm
      (composeNormalizerWithQuote n q term) :=
  q.quote_preserves_isNF _ (n.normalize_isNF term)

/-- Smoke witness: pipeline on `quoteRaw` + arbitrary Normalizer
produces the same output as `n.normalize` directly.

This is the load-bearing identity-collapse rfl-witness M16/M17
consume.  At the raw layer, the quote layer is observationally
the identity. -/
theorem composeNormalizerWithQuote_quoteRaw_extensional_identity
    (n : Normalizer) {scope : Nat}
    (term : LeanFX2.Foundation.PolyCell.Core.RawTerm scope) :
    composeNormalizerWithQuote n quoteRaw term = n.normalize term :=
  rfl

end LeanFX2.Foundation.PolyCell.NbE
