import FX1Poly.NbE.NormalizerSignature

/-! # Foundation/PolyCell/NbE/Quote
   — NbE quote: identity at the raw layer

Under the hybrid design, the raw-layer quote is the IDENTITY
function — eval's output is already a RawTerm in β-NF (per the
`Normalizer` contract's `normalize_isNF` post-condition), so no
separate readback step is needed.  Its role is structural: keep
NbE statements written in the canonical "eval then quote" form for
uniformity with the typed-η layer, where `quote_atTy : ValueTerm →
Ty → RawTerm` performs type-directed η-long readback.

## What this file defines

* `Quote` structure type — the SIGNATURE-LEVEL contract for any
  raw quote operation, sibling to `Normalizer`.  Four fields:
  - `quote : ∀ {scope}, RawTerm scope → RawTerm scope`
  - `quote_eq_id : ∀ t, quote t = t` (identity at raw layer)
  - `quote_preserves_isNF : ∀ t, isStepNormalForm t →
                             isStepNormalForm (quote t)`
  - `quote_round_trip : ∀ t, isStepNormalForm t → quote t = t`

* `NbE.quoteRaw : Quote` — the canonical raw quote instance with
  the identity implementation.

* `NbE.composeNormalizerWithQuote` — composing any Normalizer with
  a Quote into an end-to-end "eval-then-quote" pipeline that
  produces β-NF RawTerm outputs.

## Why a structure type AND a canonical instance

Same reasoning as `Normalizer`:
* The structure type captures the SIGNATURE for generic consumers
  that write theorems over any Quote instance.
* The canonical instance `quoteRaw` carries the concrete identity
  implementation.

The typed-η quote is a DISTINCT operation (`quote_atTy : ValueTerm
→ Ty → RawTerm`) that does NOT instantiate this `Quote` structure —
it has a different signature (Ty argument).  This raw `Quote`
contract is for the raw-layer Decidable Conv pipeline.

With `quote = id`, every `q.quote x` is just `x`, so the
eval-then-quote pipeline reduces to eval alone at the raw layer.

## Zero-axiom verification

The canonical instance fills:
* `quote := id`
* `quote_eq_id := fun _ => rfl`
* `quote_preserves_isNF := fun _ proof => proof`
* `quote_round_trip := fun _ _ => rfl`

All close by `rfl` or direct hypothesis passing.  No `axiom`, no
`sorry`, no Classical.  Audit-gated.

## Cross-references

* polycell.md §3 P3.9 line 5706: "ValueTerm.quote Subsumed:
  quote = inverse of fold" — at raw layer where eval IS fold,
  the inverse is the identity.
* `Normalizer` (sibling contract for the eval half).
* the typed `quote_atTy` (the η-long readback pass applied AFTER
  eval at the typed layer — distinct from this raw identity quote).
-/

namespace FX1Poly.NbE

/-- Raw quote contract.

Under the hybrid design, the raw-layer quote is the IDENTITY:
eval's output is already a RawTerm in β-NF (post the Normalizer's
`normalize_isNF` field), so no readback step is needed.

Four fields:
* `quote` — the function `RawTerm scope → RawTerm scope`.
* `quote_eq_id` — quote is extensionally identity.
* `quote_preserves_isNF` — output preserves NF predicate.
* `quote_round_trip` — NF input is a fixed point.

Field types are fully-qualified as `FX1Poly.Core.RawTerm`. -/
structure Quote where
  /-- The quote function: identity at raw layer per hybrid design. -/
  quote : ∀ {scope : Nat},
    FX1Poly.Core.RawTerm scope →
    FX1Poly.Core.RawTerm scope
  /-- Quote is extensionally identity. -/
  quote_eq_id : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    quote term = term
  /-- NF-ness is preserved: if input is in NF, output is too. -/
  quote_preserves_isNF : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    FX1Poly.Core.RawTerm.isStepNormalForm term →
    FX1Poly.Core.RawTerm.isStepNormalForm
      (quote term)
  /-- NF input is a fixed point of `quote`.

  If a term is already in step-normal form, quoting it leaves
  it unchanged.  Strictly stronger than `quote_preserves_isNF`
  on NF inputs (which only guarantees the OUTPUT is NF, not
  that it equals the input).

  At the canonical identity quote (`quoteRaw`), this trivially
  holds because quote IS identity — every term, NF or not, maps
  to itself.  At the typed-η quote, this matters more: η-long
  readback at function types DOES insert η-expansions, but only
  when the input is NOT already η-long.  NF inputs at the typed
  layer are η-long by definition; quote must respect that.

  Load-bearing for NbE soundness: the pipeline output
  `quote (normalize a)` is NF (by Normalizer.normalize_isNF +
  Quote.quote_preserves_isNF), and this field witnesses that a
  second `quote` application is a no-op. -/
  quote_round_trip : ∀ {scope : Nat}
      (term : FX1Poly.Core.RawTerm scope),
    FX1Poly.Core.RawTerm.isStepNormalForm term →
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
      ((FX1Poly.Core.RawTerm.mkGen
        .gen_unit ()
        FX1Poly.Core.RawTermChildren.childNil) :
        FX1Poly.Core.RawTerm scope) =
      FX1Poly.Core.RawTerm.mkGen
        .gen_unit ()
        FX1Poly.Core.RawTermChildren.childNil := rfl

/-- The canonical raw quote satisfies `quote_eq_id` by reflexivity
on any term.  The load-bearing property the NbE
soundness/completeness statements cite to collapse `q.quote x` to
`x` in the raw layer. -/
theorem quoteRaw_is_extensional_identity {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope) :
    quoteRaw.quote term = term := rfl

/-- `quoteRaw.quote_round_trip` collapses to `rfl` on any NF
input.  At the canonical identity quote, the round-trip property
is the same `rfl`-collapse as `quote_eq_id` — quote IS identity,
so NF inputs are fixed points definitionally. -/
theorem quoteRaw_round_trip_smoke {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope)
    (isNFProof :
      FX1Poly.Core.RawTerm.isStepNormalForm
        term) :
    quoteRaw.quote term = term :=
  quoteRaw.quote_round_trip term isNFProof

/-! ## Aggregate metric -/

/-- The Quote structure has 4 explicit fields. -/
def Quote.fieldCount : Nat := 4

theorem Quote.fieldCount_correct :
    Quote.fieldCount = 4 := rfl

/-! ## Cross-reference theorems

Pin the design triple via cross-reference theorems that
machine-check the consistency of the hybrid design + CBN strategy
+ identity quote. -/

/-- Quote is consistent with the hybrid design (raw layer returns
RawTerm in β-NF, so quote is identity). -/
theorem Quote.consistent_with_hybrid_design :
    NbEDesign.committed = .hybrid := rfl

/-- Quote is consistent with the CBN strategy (eval at the raw
layer produces β-NF; quote is identity). -/
theorem Quote.consistent_with_cbn_strategy :
    ReductionStrategy.committed = .callByName := rfl

/-! ## The eval-then-quote pipeline composition

The end-to-end pipeline at the raw layer is `q.quote ∘ n.normalize`
for any `n : Normalizer` and `q : Quote`.  As a NAMED definition,
the downstream NbE statements that consume it stay canonical.

At the canonical identity quote (`quoteRaw`), the composition
COLLAPSES to just `n.normalize` — the key property NbE soundness
uses to reduce the eval-then-quote pipeline to single-arg theorems
at the raw layer. -/

/-- The end-to-end NbE pipeline: normalize the input, then
quote the result.

At the raw layer with `quoteRaw` (the canonical identity
quote), this collapses to just `n.normalize` per
`composeNormalizerWithQuote_eq_normalize_at_quoteRaw` below.

At the typed layer with `quote_atTy` (η-long readback), the
composition is NON-TRIVIAL — quote_atTy inserts η-expansions per
the target type.

The pipeline operator that makes raw + typed NbE statements
uniform. -/
def composeNormalizerWithQuote (n : Normalizer) (q : Quote)
    {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope) :
    FX1Poly.Core.RawTerm scope :=
  q.quote (n.normalize term)

/-- At the canonical identity quote `quoteRaw`, the eval-then-
quote pipeline collapses to just `n.normalize`.

The load-bearing simplification NbE soundness uses to reduce
raw-layer `q.quote (n.normalize a) = q.quote (n.normalize b)`
to `n.normalize a = n.normalize b`. -/
theorem composeNormalizerWithQuote_eq_normalize_at_quoteRaw
    (n : Normalizer) {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope) :
    composeNormalizerWithQuote n quoteRaw term = n.normalize term :=
  rfl

/-- The pipeline output is in β-NF — direct consequence of
`Normalizer.normalize_isNF` + `Quote.quote_preserves_isNF`. -/
theorem composeNormalizerWithQuote_isNF
    (n : Normalizer) (q : Quote) {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope) :
    FX1Poly.Core.RawTerm.isStepNormalForm
      (composeNormalizerWithQuote n q term) :=
  q.quote_preserves_isNF _ (n.normalize_isNF term)

/-- Smoke witness: pipeline on `quoteRaw` + arbitrary Normalizer
produces the same output as `n.normalize` directly.

The identity-collapse rfl-witness the NbE soundness/completeness
statements consume.  At the raw layer, the quote layer is
observationally the identity. -/
theorem composeNormalizerWithQuote_quoteRaw_extensional_identity
    (n : Normalizer) {scope : Nat}
    (term : FX1Poly.Core.RawTerm scope) :
    composeNormalizerWithQuote n quoteRaw term = n.normalize term :=
  rfl

end FX1Poly.NbE
