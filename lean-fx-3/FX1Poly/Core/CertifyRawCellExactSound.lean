import FX1Poly.Core.CertifyRawCellExact
import FX1Poly.Core.PolyCellErasure

/-! # Foundation/PolyCell/Core/CertifyRawCellExactSound — raw-indexed soundness (type-level)

This file ships `certifyRawCellExact?_sound`: the **type-level
no-laundering observation** for the raw-indexed certifier.

## What this theorem proves

This theorem's body is `rfl` and the `_accepted` hypothesis is
unused.  It proves a TYPE-LEVEL property (the return type already
pins `rawCell` to the input), not a behavioral property of the
certifier's dispatch logic.

A regression that broke the certifier's behavioral dispatch
(e.g., the `.identityCell` arm returning a `.generatingCell`-shaped
output) could pass `_sound` unchanged, because the type system
still rejects malformed shapes regardless of what the dispatcher
computes.

The behavioral half of soundness — pinning the certifier's actual
dispatch arm output against the input ctor — lives in companion
files:

* `CertifyRawCellExactShape.lean` — shape pin lemmas
  (`certifyRawCellExact?_identityCell_boundary`, etc.) that DO
  inspect the acceptance hypothesis and discharge case splits on
  the recursive call's result.
* `CertifyRawCellExactCompHRejects.lean` — totality-off-compH
  (the rejection-branch shape pin).

`_sound` plus the shape pin family together close the soundness
story: type-level no-laundering + behavioral dispatch verification.

## Why the type-level theorem still ships

The architectural payoff of the raw-INDEXED return type:

```
def certifyRawCellExact? scope raw :
    Except CellCheckRejection (CertifiedRawCell profile scope raw)
```

The output type already pins `rawCell := raw` at the type level.
Any `CertifiedRawCell profile scope raw` value's `certifiedCell`
field has type `PolyCell profile sort raw.dim scope boundary raw`.
The `PolyCell.raw` extractor returns the implicit `rawCell` index,
so for any certified cell its `.raw` equals `raw` by definition.

This is the "no laundering" property MADE STRUCTURAL: any cell
produced by the certifier (or by any other means, given the type
constraint) carries the input rawCell as a type-level witness.

The `_accepted` hypothesis is included for documentation; the proof
itself ignores it (the proof is `rfl`, not a case analysis on the
acceptance).  The hypothesis lets callers transport an acceptance
result into a raw-equality conclusion in dependent contexts where
the type-level indexing alone isn't enough.

## Closing the no-false-positive guarantee

Combined with:
* `certifyRawCellExact?_compH_rejects` — the totality-off-compH
  theorem (behavioral shape pin for the reject branch).
* `certifyRawCellExact?_identityCell_boundary` and other shape
  lemmas in `CertifyRawCellExactShape.lean` — behavioral shape
  pins for the ok branches.
* `inferRawCellGeneral?_sound` — the existential-variant soundness.

this theorem closes the no-false-positives guarantee on the
raw-indexed ingress.  The existential-variant theorems extend the
guarantee to the dim-erased result type, where the raw-equality is
HEq (heterogeneous) rather than definitional.

## Zero-axiom verification

Proof is `rfl`.  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Soundness — no false positives: an accepted exact certification
yields a certified cell whose raw erasure is EXACTLY the input.

This is the raw-indexed half of the no-false-positives guarantee.
The proof closes by `rfl` because the raw-indexed return type
already pins `rawCell` to the input at the type level, and
`PolyCell.raw` is a definitional extractor of that type index.

The `_accepted` hypothesis is unused in the proof (the conclusion
holds for ANY inhabitant of `CertifiedRawCell profile scope raw`,
not just those produced by an accepted call).  It exists to let
callers thread acceptance proofs through this theorem in dependent
contexts. -/
theorem certifyRawCellExact?_sound {profile : PolyProfile} {scope : Nat}
    {rawCell : RawCell scope}
    (certifiedCell : CertifiedRawCell profile scope rawCell)
    (_accepted :
      certifyRawCellExact? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  rfl

end FX1Poly.Core
