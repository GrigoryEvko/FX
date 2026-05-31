import FX1Poly.Core.InferRawCellGeneral

/-! # Foundation/PolyCell/Core/CheckRawCellAs — expected-shape checker

This file ships `checkRawCellAs?`: the expected-sort variant of
`inferRawCellGeneral?`.  Where the general inference accepts ANY sort
the certifier produces, this checker takes an EXPECTED sort as input
and rejects with `.wrongSort` if the certifier's inferred sort
differs.

## Why a separate function — the .wrongSort rejection class

Per `polycell.md` §4's rejection taxonomy:

> | accepted inferred sort differs from expected sort in
>   `checkRawCellAs?` | reject `wrongSort` |

`.wrongSort` is a rejection class SPECIFIC to expected-shape
checking.  Bare `inferRawCellGeneral?` has no external sort
expectation; it fails with `.unknownGenerator`, `.badPayload`,
`.wrongChildShape`, `.badBoundaryEndpoint`, `.badVerticalBoundary`,
`.unsupportedCompH`, or `.unsupportedCertification` — but NEVER
`.wrongSort`.

This separation keeps the two ingress modes' rejection vocabularies
clean: bare inference fails for STRUCTURAL reasons, expected-shape
checking fails for STRUCTURAL OR EXPECTATION-MISMATCH reasons.

## One-phase design

`checkRawCellAs?` uses a ONE-PHASE design:

1. `inferRawCellGeneral?` — full certification
2. Check the result's sort against expected

The single-phase approach trades a small amount of work (certifying
the body of a mismatched-sort cell) for simpler architecture (no
separate sort-only screening function).  Under fxProfile the cost
difference is negligible since most cells the checker sees are
already expected to match (callers know the sort they're passing).

## Zero-axiom verification

All declarations use propext-free patterns:
* Match on `Except` (closed inductive)
* `if-then-else` with explicit `DecidableEq CellSort` (auto-derived,
  audited zero-axiom)
* Direct return of unmodified result struct on sort match

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Expected-shape variant of `inferRawCellGeneral?`.

Takes an `expectedSort` and runs the general certifier; if the
certifier's inferred sort matches the expected, returns the result;
if not, rejects with `.wrongSort`.

Any rejection from the underlying `inferRawCellGeneral?` passes
through unchanged.  This is the canonical ingress for callers that
know the sort they expect (e.g. typechecker-driven uses where the
calling context constrains the cell's sort). -/
def checkRawCellAs? {profile : PolyProfile}
    (expectedSort : CellSort) (expectedScope : Nat)
    (raw : RawCell expectedScope) :
    Except CellCheckRejection
      (CertifiedRawCellResult profile expectedScope) :=
  match inferRawCellGeneral? expectedScope raw with
  | .error rejection => .error rejection
  | .ok result =>
      if result.cellSort = expectedSort then
        .ok result
      else
        .error .wrongSort

end FX1Poly.Core
