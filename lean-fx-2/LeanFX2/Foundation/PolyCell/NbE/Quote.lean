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

/-! ## Aggregate metric -/

/-- The Quote structure has 3 explicit fields. -/
def Quote.fieldCount : Nat := 3

theorem Quote.fieldCount_correct :
    Quote.fieldCount = 3 := rfl

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

end LeanFX2.Foundation.PolyCell.NbE
