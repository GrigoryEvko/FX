import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralV2

/-! # Foundation/PolyCell/Core/CheckRawCellAsV2 — expected-shape checker

This file ships `checkRawCellAsV2?`: the expected-sort variant of
`inferRawCellGeneralV2?` (#163).  Where the general inference accepts
ANY sort the certifier produces, this checker takes an EXPECTED sort
as input and rejects with `.wrongSort` if the certifier's inferred
sort differs.

Direct v2 counterpart to v1's `checkRawCellAs?`
(`Core/Check.lean:2103`).

## Why a separate function — the .wrongSort rejection class

Per `polycell.md` §4's rejection taxonomy:

> | accepted inferred sort differs from expected sort in
>   `checkRawCellAs?` | reject `wrongSort` |

`.wrongSort` is a rejection class SPECIFIC to expected-shape
checking.  Bare `inferRawCellGeneralV2?` has no external sort
expectation; it fails with `.unknownGenerator`, `.badPayload`,
`.wrongChildShape`, `.badBoundaryEndpoint`, `.badVerticalBoundary`,
`.unsupportedCompH`, or `.unsupportedCertification` — but NEVER
`.wrongSort`.

This separation keeps the two ingress modes' rejection vocabularies
clean: bare inference fails for STRUCTURAL reasons, expected-shape
checking fails for STRUCTURAL OR EXPECTATION-MISMATCH reasons.

## One-phase vs two-phase design

v1's `checkRawCellAs?` uses a TWO-PHASE design:

1. `screenRawCell?` — cheap sort-only screening
2. If sort matches, `inferRawCell?` — full certification

The screen is cheaper than full certification, so v1 avoids
certifying cells that wouldn't match the expected sort anyway.

v2's `checkRawCellAsV2?` uses a ONE-PHASE design:

1. `inferRawCellGeneralV2?` — full certification
2. Check the result's sort against expected

The single-phase approach trades a small amount of work (certifying
the body of a mismatched-sort cell) for simpler architecture (no
separate `screenRawCellV2?` function).  Under fxProfile the cost
difference is negligible since most cells the checker sees are
already expected to match (callers know the sort they're passing).

Future profiles where mismatched-sort cells are common can revisit
this design and add a `screenRawCellV2?` companion.

## Zero-axiom verification

All declarations use propext-free patterns:
* Match on `Except` (closed inductive)
* `if-then-else` with explicit `DecidableEq CellSort` (auto-derived,
  audited zero-axiom at L0 #122)
* Direct return of unmodified result struct on sort match

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Expected-shape variant of `inferRawCellGeneralV2?`.

Takes an `expectedSort` and runs the general certifier; if the
certifier's inferred sort matches the expected, returns the result;
if not, rejects with `.wrongSort`.

Any rejection from the underlying `inferRawCellGeneralV2?` passes
through unchanged.  This is the canonical ingress for callers that
know the sort they expect (e.g. typechecker-driven uses where the
calling context constrains the cell's sort). -/
def checkRawCellAsV2? {profile : PolyProfile}
    (expectedSort : CellSort) (expectedScope : Nat)
    (raw : RawCellV2 expectedScope) :
    Except CellCheckRejection
      (CertifiedRawCellResultV2 profile expectedScope) :=
  match inferRawCellGeneralV2? expectedScope raw with
  | .error rejection => .error rejection
  | .ok result =>
      if result.cellSort = expectedSort then
        .ok result
      else
        .error .wrongSort

end LeanFX2.Foundation.PolyCell.Core
