import LeanFX2.Foundation.PolyCell.Core.Check
import LeanFX2.Foundation.PolyCell.Core.NegativeProbes
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2Coverage

/-! # Foundation/PolyCell/Core/V1V2SeedVariableSpike — v1↔v2 agreement spike

V2-SPIKE-2 (2026-05-27).  Ships the **agreement spike** between v1's
`inferRawCellGeneral?` (dim-indexed PolyTerm input) and v2's
`inferRawCellGeneralV2?` (un-indexed RawCellV2 input) on the same
conceptual fixture — the **seed variable** at scope 1.

## What this spike proves

For "var 0 at scope 1", three observational agreements:

* **`v1_v2_seedVariable_sort_agree`** — `certifiedResultSort?` agrees
  between v1 and v2 outputs.  The two existentials return the same
  `Option CellSort`.
* **`v1_v2_seedVariable_sort_term`** — both `certifiedResultSort?`
  projections produce specifically `some .term` (not merely some
  matching but unspecified sort).
* **`v1_v2_seedVariable_dim_zero`** — both certifiers' `.cellDimension`
  fields are `0`.  This pins the dim-erased existential's stored
  dimension matches between v1 and v2.

Each closes by `rfl` because both certifiers are pure computations
reducing the seed-variable fixture through admission + payload
evidence + (nil for v2) spine certification to a definite Except.ok
result.

## What "the dim-erased existential" means here

Both v1's `CertifiedRawCellResult` and v2's `CertifiedRawCellResultV2`
are EXISTENTIAL packages — they bundle the cell's dimension as a
data field rather than as a type-level index.  Observationally,
both export `.cellSort` and `.cellDimension`.

The spike pins agreement at this **observational** layer.  Direct
equality of the certified inhabitants (the `PolyCell` vs
`PolyCellV2` values inside the existentials) is NOT proven and
cannot be proven without translation (the two inductives are
structurally distinct).

## Why the spike matters

Per the polycell.md migration plan, V2-bridge.* tasks need a
translation layer (v1 -> v2 or v2 -> v1) before v2 can replace v1
across the rest of the codebase.  The agreement spike is the
**linchpin** that justifies the bridge:

* If v1 and v2 disagree even on observational sort / dimension, the
  bridge isn't possible without semantic reconciliation.
* If they agree (this spike), the bridge work becomes mechanical:
  v2 fixtures are equivalent to v1 fixtures modulo translation,
  and existing v1 consumers can be re-pointed via the translation.

## Why the seed variable specifically

The "seed variable" — `var 0` at scope 1 — is the **simplest
non-trivial fixture**:

* It's not a closed term (it references a free variable, exercising
  the `Fin scope` payload path).
* It's not a unit / constant (it exercises the gen_var generator
  specifically, distinct from gen_unit etc.).
* It's at scope 1 (the minimum scope where var 0 is well-formed).

v1's fixture is `NegativeProbes.seedTermAtom fxProfile :
PolyTerm fxProfile 0`, defined at `Core/NegativeProbes.lean:262` as
`.atom variableGeneratorSpec.cellId 0` — cellId 0 (the variable
generator) with payload 0 (the index).

v2's fixture is `CoverageV2.varZeroRaw : RawCellV2 1`, defined at
`Core/CertifyRawCellExactV2Coverage.lean:105` as
`.termBase (.mkGen .gen_var ⟨0, _⟩ .childNil)` — `gen_var` generator
with payload `⟨0, _⟩ : Fin 1`.

Despite the structural differences in representation, both denote
the same conceptual entity: the variable at de Bruijn index 0 in a
context of length 1.

## What's NOT shipped here

* **A translation function** between v1's PolyTerm and v2's
  RawCellV2.  That's V2-bridge.1 / V2-bridge.2.
* **A roundtrip lemma** showing `toV2 (toV1 raw) = raw`.  That's
  V2-bridge.3.
* **Per-fixture agreement extended to all 15 V2 coverage fixtures**.
  That's V2-bridge.4, which can mechanically reuse this spike's
  pattern (rfl-based `certifiedResultSortV2? ... = certifiedResultSort? ...`
  for every covered v1↔v2 fixture pair).

The spike establishes the PATTERN; the bridge tasks generalize and
formalize it.

## Zero-axiom verification

All three agreement theorems pass `#assert_no_axioms`.  Audit-gated
in `Tools/AuditAll/AuditPolyCell.lean`.

## Avoided propext trap

A naive `match ... | Except.ok x => some x.dim | _ => none`
formulation in `v1_v2_seedVariable_dim_zero` leaks `propext` through
Lean's match equation lemmas (see
`feedback_lean_zero_axiom_match`).  The shipped version uses full
enumeration `Except.ok x => ... | Except.error _ => ...` to stay
clean.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **v1↔v2 sort agreement on the seed variable.**

Both v1's and v2's general ingress, called on the seed-variable
fixture at scope 1, return the SAME sort projection (an
`Option CellSort`).

Closes by `rfl`: both reduce to `some .term`. -/
theorem v1_v2_seedVariable_sort_agree :
    Check.certifiedResultSort?
        (Check.inferRawCellGeneral? (profile := fxProfile) 1
          (NegativeProbes.seedTermAtom fxProfile))
      = certifiedResultSortV2?
          (inferRawCellGeneralV2? (profile := fxProfile) 1
            CoverageV2.varZeroRaw) := rfl

/-- **v1↔v2 sort agreement at the EXPECTED value `.term`.**

Both projections produce specifically `some .term` (not merely some
matching but unspecified sort).  A regression that broke the sort
accounting on either side would fail one half of this conjunction. -/
theorem v1_v2_seedVariable_sort_term :
    Check.certifiedResultSort?
        (Check.inferRawCellGeneral? (profile := fxProfile) 1
          (NegativeProbes.seedTermAtom fxProfile))
      = some CellSort.term
    ∧
    certifiedResultSortV2?
        (inferRawCellGeneralV2? (profile := fxProfile) 1
          CoverageV2.varZeroRaw)
      = some CellSort.term := ⟨rfl, rfl⟩

/-- **v1↔v2 dimension agreement: both produce cellDimension 0.**

Both v1's and v2's certified-result existentials store
`cellDimension := 0` for the seed variable.  Witnesses that the
dim-erased layer agrees on the structural fact "seed variable is
dim 0".

Uses full Except enumeration (Ok + Error) rather than a wildcard
`_ => none` to avoid propext leakage through Lean's match equation
lemmas. -/
theorem v1_v2_seedVariable_dim_zero :
    (match Check.inferRawCellGeneral? (profile := fxProfile) 1
              (NegativeProbes.seedTermAtom fxProfile) with
     | Except.ok result => some result.cellDimension
     | Except.error _ => none) = some 0
    ∧
    (match inferRawCellGeneralV2? (profile := fxProfile) 1
              CoverageV2.varZeroRaw with
     | Except.ok result => some result.cellDimension
     | Except.error _ => none) = some 0 := ⟨rfl, rfl⟩

end LeanFX2.Foundation.PolyCell.Core
