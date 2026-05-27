import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2
import LeanFX2.Foundation.PolyCell.Core.PolyCellV2Erasure

/-! # Foundation/PolyCell/Core/CertifyRawCellExactV2Sound — raw-indexed soundness

This file ships `certifyRawCellExactV2?_sound`: the no-false-positive
theorem for the raw-indexed certifier (#162).  Every accepted
certification yields a certified cell whose raw erasure is EXACTLY
the input — the certifier cannot launder a different raw past the
input.

Direct v2 counterpart to v1's `certifyRawCellExact?_sound`
(`Core/CertifyExact.lean:132`).

## Why this theorem is `rfl`

The architectural payoff of v2's raw-INDEXED return type:

```
def certifyRawCellExactV2? scope raw :
    Except CellCheckRejection (CertifiedRawCellV2 profile scope raw)
```

The output type already pins `rawCell := raw` at the type level.
Any `CertifiedRawCellV2 profile scope raw` value's `certifiedCell`
field has type `PolyCellV2 profile sort raw.dim scope boundary raw`.
The `PolyCellV2.raw` extractor returns the implicit `rawCell` index,
so for any certified cell its `.raw` equals `raw` by definition.

This is the "no laundering" property MADE STRUCTURAL: any cell
produced by the certifier carries the input rawCell as a type-level
witness; there is literally no way for the certifier to return a
certificate over a different raw.

The `_accepted` hypothesis is included for documentation and to
match the v1 theorem signature; the proof itself ignores it
(witness: the proof is `rfl`, not a case analysis on the
acceptance).  The hypothesis lets callers transport an acceptance
result into a raw-equality conclusion in dependent contexts where
the type-level indexing alone isn't enough.

## Closing the no-false-positive guarantee

Combined with:
* `certifyRawCellExactV2?_compH_rejects` (#166) — the totality-off-compH
  theorem
* `inferRawCellGeneralV2?_sound` (#169) — the existential-variant
  soundness

this theorem closes the no-false-positives guarantee on the
raw-indexed ingress.  The existential-variant theorems (#167-#169)
extend the guarantee to the dim-erased result type, where the
raw-equality is HEq (heterogeneous) rather than definitional.

## Zero-axiom verification

Proof is `rfl`.  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Soundness — no false positives: an accepted exact certification
yields a certified cell whose raw erasure is EXACTLY the input.

This is the raw-indexed half of the no-false-positives guarantee.
The proof closes by `rfl` because the raw-indexed return type
already pins `rawCell` to the input at the type level, and
`PolyCellV2.raw` is a definitional extractor of that type index.

The `_accepted` hypothesis is unused in the proof (the conclusion
holds for ANY inhabitant of `CertifiedRawCellV2 profile scope raw`,
not just those produced by an accepted call).  It exists to match
v1's theorem signature and to let callers thread acceptance proofs
through this theorem in dependent contexts. -/
theorem certifyRawCellExactV2?_sound {profile : PolyProfile} {scope : Nat}
    {rawCell : RawCellV2 scope}
    (certifiedCell : CertifiedRawCellV2 profile scope rawCell)
    (_accepted :
      certifyRawCellExactV2? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  rfl

end LeanFX2.Foundation.PolyCell.Core
