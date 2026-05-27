import LeanFX2.Foundation.PolyCell.Core.CheckRawCellAs
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactCoverage

/-! # CertifyRawCellExactNegativeProbes — rejection-side coverage suite

This file ships the negative-probe suite for the v2 ingress: the dual
of #170's positive coverage.  Where #170 proves the certifier ACCEPTS
well-formed fixtures with the expected sort, this file proves the
certifier REJECTS malformed fixtures with the expected rejection
reason.

Direct v2 counterpart to v1's rejection-family headlines at
`Core/CertifyExact.lean:99-109`
(`inferRawCellGeneral?_unknownGenerator_rejects`,
`inferRawCellGeneral?_compH_rejects`, ...).

## The rejection-side guarantee

Soundness (#165-#169) proves the certifier never accepts BADLY: every
accepted certification faithfully reflects its input.  But soundness
alone could be vacuously satisfied by a certifier that ALWAYS REJECTS.

The negative probes are the dual: they prove specific malformed inputs
trigger the EXPECTED rejection reason.  Together with positive
coverage (#170), they triangulate the certifier's decision boundary:

* **Soundness (#165-#169)**: if accepted, the cell is faithful
* **Positive coverage (#170)**: well-formed fixtures ARE accepted
* **Negative coverage (this file)**: malformed fixtures ARE rejected

## The reachable-rejection landscape under fxProfile

Under v2 with `fxProfile` (all 194 generators admitted), three
rejection branches are runtime-reachable:

* `.unsupportedCompH` — `.horizontalComposite _ _` always rejects
  (Gray-tensor semantics pending Axis 6).
* `.badVerticalBoundary` — `.verticalComposite first second` where
  `first.dim = 0` (all `.termBase _` have dim 0) or `first.dim != second.dim`.
* `.wrongSort` — `checkRawCellAs?` with expectedSort != inferred sort.

The remaining seven rejection branches in `CellCheckRejection.all` are
forward-compat dead code under fxProfile:

* `.unknownGenerator` — `supportedGenerator?` always returns `some`
  under fxProfile (all 194 admitted).  Restricted profiles (e.g.
  "no-HoTT FX") refine `SupportedGenerator` with fewer arms,
  activating this branch.
* `.badPayload` — `genPayloadEvidence?` always returns `some` under
  fxProfile (every payload admitted).  Restricted profiles refine
  `GenPayloadEvidence` with discriminating bodies.
* `.wrongChildShape` — under fxProfile, every child spec has sort
  `.term` and `cellDimension 0`, matching every termBase child's
  inferred shape.  Reachable only under future profiles with
  cross-sort spine semantics.
* `.fuelExhausted` — top-level wrapper supplies `raw.size + 1` fuel,
  always sufficient.  Reachable only from direct callers of
  `certifyRawCellExactFueled?` with insufficient fuel.
* `.badBoundaryEndpoint`, `.unsupportedCertification` — used by v2's
  `buildGeneratingCellExact?` and reserved for future ingress
  extensions; dead code under the current fxProfile ingress surface.

The fxProfile-reachable trio (`.unsupportedCompH`,
`.badVerticalBoundary`, `.wrongSort`) covers every rejection branch
exercisable from the public ingress API.  Future restricted-profile
test suites will activate the dead-code branches without changing
this file's `rfl`-proved theorems.

## Why `rfl` works

Each rejection theorem closes by `rfl` because the certifier is a
pure computation: given a closed malformed RawCell input, it reduces
via the fuel wrapper + structural dispatch to a definite `Except.error
<rejection>` value.

The reduction chain for `.unsupportedCompH`:

1. `inferRawCellGeneral? scope rawCell` → matches on `certifyRawCellExact?`
2. `certifyRawCellExact? scope rawCell`
   → `certifyRawCellExactFueled? (rawCell.size + 1) scope rawCell`
3. fuel = `Nat.succ _`, matches `fuel' + 1` arm
4. Inner match on `rawCell` hits `.horizontalComposite _ _`
5. Returns `.error .unsupportedCompH`
6. Wrapper passes through: `.error .unsupportedCompH`
7. `certifiedResultRejection?` projects: `some .unsupportedCompH`

The reduction chain for `.badVerticalBoundary`:

1-3. Same as above
4. Inner match on `rawCell` hits `.verticalComposite first second`
5. Recursively certify `first` and `second` (both certify cleanly)
6. Match on `first.dim` — both children are `.termBase`, so `first.dim = 0`
7. Hits `| 0 => .error .badVerticalBoundary`
8. Wrapper passes through

The reduction chain for `.wrongSort`:

1. `checkRawCellAs? .type 0 unitTermRaw`
2. Calls `inferRawCellGeneral? 0 unitTermRaw`
3. Unit term cert returns `.ok { cellSort := .term, ... }` (per #170)
4. Sort check: `result.cellSort = .term`, expected `.type`, mismatch
5. Returns `.error .wrongSort`

All three chains close by definitional reduction in `rfl`.

## Zero-axiom verification

All declarations propext-free:
* Negative fixture raw cells are pure data (struct construction)
* Rejection theorems close by `rfl`
* The `certifiedResultRejection?` helper is a one-line `def`
  matching on Except

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Extract the rejection reason from an Except-valued certified result.

Dual of `certifiedResultSort?` (#170).  Where the positive coverage
helper projects the sort on acceptance, this helper projects the
rejection reason on rejection.  Both return `Option` so coverage
theorems can compare against expected outcomes uniformly via `rfl`. -/
def certifiedResultRejection? {profile : PolyProfile} {scope : Nat} :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) →
      Option CellCheckRejection
  | Except.ok _ => none
  | Except.error rejection => some rejection

namespace NegativeProbes

/-- A horizontal composite of two unit term-bases at scope 0.

  `horizontalCompositeUnitRaw =
    .horizontalComposite
      (.termBase (.mkGen .gen_unit () .childNil))
      (.termBase (.mkGen .gen_unit () .childNil))`

The simplest fixture triggering `.unsupportedCompH` — the certifier
unconditionally rejects every `.horizontalComposite _ _` regardless of
operand structure (Gray-tensor semantics pending Axis 6).  Both
operands are well-formed unit terms, so the rejection is purely about
the cell-layer constructor, not the children. -/
def horizontalCompositeUnitRaw : RawCell 0 :=
  .horizontalComposite
    (.termBase (.mkGen .gen_unit () .childNil))
    (.termBase (.mkGen .gen_unit () .childNil))

/-- A vertical composite of two unit term-bases at scope 0.

  `verticalCompositeUnitRaw =
    .verticalComposite
      (.termBase (.mkGen .gen_unit () .childNil))
      (.termBase (.mkGen .gen_unit () .childNil))`

The simplest fixture triggering `.badVerticalBoundary`.  Both operands
certify cleanly as unit terms (per #170), but every `.termBase _` has
computed `dim = 0`, so the certifier's `match first.dim with | 0`
branch fires — vertical composition is only well-defined at `dim >= 1`.

This is the "no dim-0 vertical composite" guard: vertical composition
of 0-cells is meaningless in a higher category (0-cells have no
boundary to compose along).  The certifier rejects structurally
rather than admitting nonsense. -/
def verticalCompositeUnitRaw : RawCell 0 :=
  .verticalComposite
    (.termBase (.mkGen .gen_unit () .childNil))
    (.termBase (.mkGen .gen_unit () .childNil))

end NegativeProbes

/-- The `horizontalCompositeUnit` fixture rejects with `.unsupportedCompH`
through the general existential ingress.

Closes by `rfl`: the `.horizontalComposite _ _` certifier arm
unconditionally returns `.error .unsupportedCompH` without recursing
into the operands.  This is the architectural marker that v2 does not
yet implement horizontal composition — Axis 6's Gray-tensor semantics
must land first. -/
theorem negative_horizontalCompositeUnit_rejects_unsupportedCompH
    {profile : PolyProfile} :
    certifiedResultRejection?
      (inferRawCellGeneral? (profile := profile) 0
        NegativeProbes.horizontalCompositeUnitRaw) =
      some .unsupportedCompH := rfl

/-- The `verticalCompositeUnit` fixture rejects with `.badVerticalBoundary`
through the general existential ingress.

Closes by `rfl`: both operands certify (per #170), but `first.dim = 0`
triggers the certifier's vertical-composite guard.  Dim-0 cells cannot
be vertically composed (they have no boundary along which to compose).

The deep-trace is non-trivial — the certifier recursively certifies
both operands (each producing `.ok` with `cellSort := .term, dim := 0`)
before reaching the boundary check.  Yet the entire trace reduces
definitionally; `rfl` succeeds at unfolding the full evaluation. -/
theorem negative_verticalCompositeUnit_rejects_badVerticalBoundary
    {profile : PolyProfile} :
    certifiedResultRejection?
      (inferRawCellGeneral? (profile := profile) 0
        NegativeProbes.verticalCompositeUnitRaw) =
      some .badVerticalBoundary := rfl

/-- The `unitTermRaw` fixture (from #170's coverage suite) rejects with
`.wrongSort` when checked against expected sort `.type`.

Closes by `rfl`: `inferRawCellGeneral?` accepts the unit term at
inferred sort `.term` (per #170's `coverage_unitTermRaw_sort`), but
`checkRawCellAs?`'s sort comparison rejects when the expected sort
is `.type`.

This is the only `.wrongSort` rejection currently reachable: bare
`inferRawCellGeneral?` has no external sort expectation and never
rejects with `.wrongSort` — the rejection class is specific to
`checkRawCellAs?`'s expected-shape contract.

Pattern note: rather than introduce a separate negative fixture,
this theorem REUSES `Coverage.unitTermRaw` from #170.  Same raw
cell, different question — coverage asks "what sort?" and gets `.term`;
negative-probe asks "is it `.type`?" and gets `.wrongSort`.  The fixture
catalog stays compact. -/
theorem negative_unitTerm_as_type_rejects_wrongSort
    {profile : PolyProfile} :
    (match checkRawCellAs? (profile := profile) .type 0 Coverage.unitTermRaw with
      | Except.ok _ => none
      | Except.error rejection => some rejection) =
      some .wrongSort := rfl

end LeanFX2.Foundation.PolyCell.Core
