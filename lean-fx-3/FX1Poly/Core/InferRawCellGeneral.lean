import FX1Poly.Core.CertifyRawCellExact
import FX1Poly.Core.RawCellCode

/-! # Foundation/PolyCell/Core/InferRawCellGeneral — existential wrapper

`inferRawCellGeneral?`: the executable existential wrapper around
`certifyRawCellExact?`.  Returns a `CertifiedRawCellResult` whose
`rawCell` is a FIELD (not a type parameter), letting callers consume
the certification result without threading the input raw through the
return type.

## Why two packages — raw-INDEXED vs EXISTENTIAL

The certifier ecosystem has two complementary package types:

* `CertifiedRawCell profile scope rawCell` (raw-INDEXED):
  rawCell is a TYPE PARAMETER.  The certificate is pinned to the
  exact input.  Used by `certifyRawCellExact?` — the
  certifier never silently changes the rawCell it certifies.

* `CertifiedRawCellResult profile scope` (EXISTENTIAL, this file):
  rawCell is a FIELD.  The package is consumable by callers that
  don't want to thread the input rawCell through the return type
  (e.g. higher-level ingress points, REST APIs, agent protocols).

The wrapper repackages a raw-indexed result into an existential one,
adding two `polycell.md` §4 spec fields:

* `inputCode : List Nat` — the prefix code of the raw input
* `hasInputCode : hasSameNatList inputCode rawCell.toCode = true`
  — a propositional certificate that the result's rawCell has the
  same prefix code as the input

These two fields enable a code-level proof of "no laundering":
later soundness theorems verify that
`inferRawCellGeneral?_sound` rules out the result's rawCell
differing from the input under the existential wrapper.

## The hasSameNatList_self prerequisite

Constructing the `hasInputCode` field requires
`hasSameNatList rawCell.toCode rawCell.toCode = true`.  This is
`hasSameNatList_self`, a self-contained lemma proven by list
induction + Nat.beq induction.  Zero-axiom verification by direct
structural pattern matching; no `simp`, no `omega`, no classical
reasoning.

## Zero-axiom verification

All declarations use propext-free structural patterns:
* `hasSameNatList_self` — nested induction on List Nat + Nat
* `CertifiedRawCellResult` — pure structural record
* `inferRawCellGeneral?` — match on Except + direct struct
  construction

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Self-reflexivity of `Nat.beq`: every Nat compares equal to
itself.  Used by `hasSameNatList_self` for the per-cell-element
comparison. -/
private theorem natBeqSelf (value : Nat) : Nat.beq value value = true := by
  induction value with
  | zero => rfl
  | succ predecessor ihPredecessor => exact ihPredecessor

/-- Self-reflexivity of `hasSameNatList`: every code list compares
equal to itself.

Used by `inferRawCellGeneral?` to construct the `hasInputCode`
witness when `inputCode := rawCell.toCode` — by reflexivity, the
two code lists are syntactically identical, so the boolean
comparison returns `true`.

Proof: list induction with nested Nat.beq reflexivity for each
head element. -/
theorem hasSameNatList_self (codes : List Nat) :
    hasSameNatList codes codes = true := by
  induction codes with
  | nil => rfl
  | cons codeHead remainingCodes ihTail =>
      show (Nat.beq codeHead codeHead && hasSameNatList remainingCodes remainingCodes) = true
      rw [natBeqSelf, ihTail]
      rfl

/-- Existential certified-result package.

Mirrors the spec at `polycell.md` §4 line 4034.

FIELDS (7 total):
* `cellDimension : Nat` — the inferred dimension (always equals
  `rawCell.dim` by construction)
* `inputCode : List Nat` — prefix code of the raw input
* `rawCell : RawCell scope` — the certified raw cell
* `cellSort : CellSort` — inferred sort
* `cellBoundary : CellBoundary profile cellSort cellDimension scope` —
  boundary data (Unit at dim 0; source/target pair at dim n+1)
* `certifiedCell : PolyCell profile cellSort cellDimension scope
  cellBoundary rawCell` — the certified cell itself
* `hasInputCode : hasSameNatList inputCode rawCell.toCode = true` —
  code-level no-laundering certificate -/
structure CertifiedRawCellResult (profile : PolyProfile) (scope : Nat) where
  /-- Dimension of the certified raw cell.  By construction equals
  `rawCell.dim` (the certifier never produces results at a dim
  inconsistent with the rawCell's structural dim). -/
  cellDimension : Nat
  /-- Prefix code of the raw input that produced this result. -/
  inputCode : List Nat
  /-- Certified raw cell returned by the ingress. -/
  rawCell : RawCell scope
  /-- Sort inferred for the certified cell. -/
  cellSort : CellSort
  /-- Boundary inferred for the certified cell. -/
  cellBoundary : CellBoundary profile cellSort cellDimension scope
  /-- Certified cell over `rawCell` at the inferred dim and sort. -/
  certifiedCell :
    PolyCell profile cellSort cellDimension scope cellBoundary rawCell
  /-- The returned raw cell has the same prefix code as the input. -/
  hasInputCode :
    hasSameNatList inputCode rawCell.toCode = true

/-- General existential ingress: wraps `certifyRawCellExact?`'s
raw-indexed result into the existential `CertifiedRawCellResult`.

The wrapper:
1. Computes `inputCode := raw.toCode`
2. Calls `certifyRawCellExact?` for the exact certification
3. On success, packages the result with `inputCode`, `hasInputCode`
   (constructed via `hasSameNatList_self`), and the three certified
   fields lifted from the raw-indexed result
4. On error, propagates the rejection unchanged

The wrapper introduces no new failure modes — every rejection from
the exact certifier passes through unchanged. -/
def inferRawCellGeneral? {profile : PolyProfile} (scope : Nat)
    (raw : RawCell scope) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  match certifyRawCellExact? scope raw with
  | .error rejection => .error rejection
  | .ok exactResult =>
      .ok {
        cellDimension := raw.dim,
        inputCode := raw.toCode,
        rawCell := raw,
        cellSort := exactResult.sort,
        cellBoundary := exactResult.boundary,
        certifiedCell := exactResult.certifiedCell,
        hasInputCode := hasSameNatList_self raw.toCode
      }

end FX1Poly.Core
