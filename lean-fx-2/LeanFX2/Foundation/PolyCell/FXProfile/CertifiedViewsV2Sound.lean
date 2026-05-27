import LeanFX2.Foundation.PolyCell.FXProfile.CertifiedViewsV2
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2Sound
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2CompHRejects
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralV2AcceptedCellDimensionEq
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralV2Sound

/-! # FXProfile/CertifiedViewsV2Sound — FX-profile soundness suite

This file ships the soundness theorems for the FX-profile entry points
(#172).  Four theorems pin the FX-profile ingress to the same
no-laundering, dim-preservation, and compH-rejection guarantees that
the general v2 API enjoys (#165, #166, #167, #169).

Direct v2 counterpart to v1's soundness suite at
`Core/CertifyExact.lean:170-191` (`certifyFXCellExact?_sound`,
`_compH_rejects`, `certifyFXCell?_accepted_cellDimension_eq`,
`certifyFXCell?_sound`).

## The four theorems

* **`certifyFXCellExactV2?_compH_rejects`** — every horizontal
  composite rejects with `.unsupportedCompH`.  The single rejection
  class for the raw-indexed FX-profile ingress (Gray-tensor semantics
  pending Axis 6).

* **`certifyFXCellExactV2?_sound`** — every cell accepted by the
  raw-indexed FX ingress erases EXACTLY to its raw input.  The
  raw-indexed signature makes this trivial: `CertifiedRawCellV2`
  carries the input as a type-level parameter, so erasure
  back to that input is `rfl` (the architectural payoff of indexing
  by the EXACT input).

* **`certifyFXCellV2?_accepted_cellDimension_eq`** — every cell
  accepted by the existential FX ingress has its dim-erased
  `cellDimension` field equal to the input raw's computed `dim`.

* **`certifyFXCellV2?_sound`** — every cell accepted by the
  existential FX ingress has its certified cell's raw erasure
  heterogeneously equal to the input.  Combined with
  `_accepted_cellDimension_eq`, this closes the no-laundering
  guarantee on the existential ingress: no accepted cell can launder
  its raw cell or its dimension through the existential wrapper.

## Why all four are one-line delegations

`certifyFXCellExactV2?` is DEFINITIONALLY `certifyRawCellExactV2?
(profile := fxProfile)` and `certifyFXCellV2?` is DEFINITIONALLY
`inferRawCellGeneralV2? (profile := fxProfile)`.  Lean's definitional
reduction sees through these wrappers without an `unfold` or `rfl`
step.  So:

* A hypothesis `certifyFXCellExactV2? scope raw = Except.ok cell` is
  the SAME proposition as `certifyRawCellExactV2? (profile := fxProfile)
  scope raw = Except.ok cell`.
* A conclusion about the FX-profile result type is the SAME conclusion
  about the general result type with profile fixed.

The base theorems apply directly with `profile := fxProfile`
instantiated — no `by` block, no rewriting, no tactic combinators.
Each FX-profile theorem's body is a single base-theorem application.

This is the trust-cost-zero payoff of definitional wrappers: every
theorem on the underlying op transfers without a re-proof obligation.

## Together with the entry points (#172), this closes L1cert.4 soundness

#165-#169 ship the general no-laundering suite for the parameterized
infrastructure.  #172 ships the FX-profile entry-point wrappers.
This commit ships the soundness lift: same theorems re-stated against
the FX-profile names, with proofs by direct delegation.

The L1cert.4 soundness story is now complete for both API surfaces:
the general (profile-parameterized) and the FX-profile (profile-fixed).

## Zero-axiom verification

Each proof is a single function application against an already
audited zero-axiom theorem.  No new reasoning is introduced.  Audit
gates live in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- The FX-profile raw-indexed certifier rejects horizontal composition
pending Gray-tensor semantics (Axis 6).

Direct delegation to `Core.certifyRawCellExactV2?_compH_rejects`
(#166) with `profile := fxProfile`.  The FX-profile call is
definitionally the general call with profile fixed, so the base
theorem applies without rewriting. -/
theorem certifyFXCellExactV2?_compH_rejects {scope : Nat}
    (leftOperand rightOperand : RawCellV2 scope) :
    certifyFXCellExactV2? scope
        (.horizontalComposite leftOperand rightOperand) =
      Except.error .unsupportedCompH :=
  certifyRawCellExactV2?_compH_rejects (profile := fxProfile)
    leftOperand rightOperand

/-- Every cell accepted by the raw-indexed FX ingress erases exactly
to its raw input — the FX-level statement of no-false-positives for
`certifyFXCellExactV2?`.

Direct delegation to `Core.certifyRawCellExactV2?_sound` (#165).
The raw-indexed signature pins the input at the type level via
`CertifiedRawCellV2 fxProfile scope rawCell`, so erasure back to the
input is `rfl` underneath. -/
theorem certifyFXCellExactV2?_sound {scope : Nat}
    {rawCell : RawCellV2 scope}
    (certifiedCell : CertifiedRawCellV2 fxProfile scope rawCell)
    (accepted :
      certifyFXCellExactV2? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  certifyRawCellExactV2?_sound certifiedCell accepted

/-- Every cell accepted by the existential FX ingress recovers the
input's computed dimension — `result.cellDimension = raw.dim`.

Direct delegation to `Core.inferRawCellGeneralV2?_accepted_cellDimension_eq`
(#167).  The dim is the FIRST projection from the existential
wrapper; this theorem locks it to the input's computed dim, ruling
out dim-laundering through the type-erasure. -/
theorem certifyFXCellV2?_accepted_cellDimension_eq {scope : Nat}
    {raw : RawCellV2 scope}
    {result : CertifiedRawCellResultV2 fxProfile scope}
    (accepted : certifyFXCellV2? scope raw = Except.ok result) :
    result.cellDimension = raw.dim :=
  inferRawCellGeneralV2?_accepted_cellDimension_eq accepted

/-- Every cell accepted by the existential FX ingress has its
certified cell's raw erasure heterogeneously equal to the input —
the FX-level statement of no-false-positives for `certifyFXCellV2?`.

Direct delegation to `Core.inferRawCellGeneralV2?_sound` (#169).
The HEq form rather than Eq is forced by the existential wrapper:
`result.certifiedCell` has its rawCell as an existentialized index,
so the rawCell equality is across different types and HEq is the
canonical comparison form.

Combined with `_accepted_cellDimension_eq`, this closes the
no-laundering guarantee on the FX-profile existential ingress: no
accepted cell can launder its raw cell, its computed dimension, or
the agreement between them through the existential wrapper. -/
theorem certifyFXCellV2?_sound {scope : Nat}
    {raw : RawCellV2 scope}
    {result : CertifiedRawCellResultV2 fxProfile scope}
    (accepted : certifyFXCellV2? scope raw = Except.ok result) :
    HEq result.certifiedCell.raw raw :=
  inferRawCellGeneralV2?_sound accepted

end LeanFX2.Foundation.PolyCell.FXProfile
