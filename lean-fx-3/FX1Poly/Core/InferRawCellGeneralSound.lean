import FX1Poly.Core.InferRawCellGeneralAcceptedRawCellHEq
import FX1Poly.Core.PolyCellErasure

/-! # InferRawCellGeneralSound — existential no-laundering keystone

`inferRawCellGeneral?_sound`: the existential-variant soundness
theorem.  When the existential wrapper accepts a raw input, the
certified cell stored in the result has its raw erasure
heterogeneously equal to the input.

## The headline guarantee

Combined with:
* `inferRawCellGeneral?_accepted_cellDimension_eq` — dim preserves
* `inferRawCellGeneral?_accepted_rawCell_heq` — raw preserves

this theorem closes the **NO-LAUNDERING** guarantee on the
existential ingress.  Every cell accepted by the existential
wrapper:

* Has its `cellDimension` field equal to `raw.dim` (Eq)
* Has its `rawCell` field heterogeneously equal to `raw` (HEq)
* Has its `certifiedCell`'s raw erasure heterogeneously equal to
  `raw` (HEq, proven by this theorem)

There is no way for the existential wrapper to return a certified
cell whose raw erasure differs from the input — the type-erasure of
the wrapper doesn't sneak a different cell through.

## The proof — two-step HEq composition

The proof composes two facts via `HEq.trans`:

1. `result.certifiedCell.raw = result.rawCell` — by definition of
   `PolyCell.raw` (the extractor returns the implicit rawCell
   index, which for `result.certifiedCell : PolyCell ... result.rawCell`
   is `result.rawCell`).  Closes by `rfl`.

2. `HEq result.rawCell raw` — by
   `inferRawCellGeneral?_accepted_rawCell_heq`.

The composition:
```
HEq.trans
  (heq_of_eq (show result.certifiedCell.raw = result.rawCell from rfl))
  (inferRawCellGeneral?_accepted_rawCell_heq accepted)
```

With the un-indexed rawCell (all types `RawCell scope`), the HEq
collapses to Eq.  The HEq form is retained for API compatibility
(see the `inferRawCellGeneral?_accepted_rawCell_heq` docstring for
the reasons).

## Zero-axiom verification

The proof uses:
* `heq_of_eq` (Eq → HEq, propext-free)
* `HEq.trans` (HEq transitivity, propext-free)
* `rfl` for the `result.certifiedCell.raw = result.rawCell` leg
* `inferRawCellGeneral?_accepted_rawCell_heq` (zero-axiom)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Existential no-false-positives: every cell accepted by the
existential wrapper erases through its certified cell to EXACTLY
the syntactic input (heterogeneously for API compatibility, though
under the un-indexed rawCell the HEq is reducible to Eq).

Keystone of the existential-variant soundness trio.  Combined with
the raw-indexed `_sound` and `_compH_rejects`, this closes the FULL
no-false-positives guarantee on the entire certifier ingress
(raw-indexed + existential). -/
theorem inferRawCellGeneral?_sound
    {profile : PolyProfile} {scope : Nat} {raw : RawCell scope}
    {result : CertifiedRawCellResult profile scope}
    (accepted :
      inferRawCellGeneral? scope raw = Except.ok result) :
    HEq result.certifiedCell.raw raw :=
  HEq.trans
    (heq_of_eq
      (show result.certifiedCell.raw = result.rawCell from rfl))
    (inferRawCellGeneral?_accepted_rawCell_heq accepted)

end FX1Poly.Core
