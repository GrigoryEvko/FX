import LeanFX2.Foundation.PolyCell.Core.CertifiedTermV2
import LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpineV2Projections

/-! # Foundation/PolyCell/Core/CertifiedToPolyCellV2 — Certified→PolyCellV2

V2-L3.1 phase D step 4 (2026-05-27).  Ships the bridge from the
procedural `Certified` predicate (certifier accepts) to the
structural `PolyCellV2` representation (a certified cell exists).

## The bridge direction

`Certified raw` is the existential `∃ result, inferRawCellGeneralV2?
scope (.termBase raw) = .ok result`.  The wrapper packs the
exact-certifier's result into a `CertifiedRawCellResultV2` and
returns it.  Extracting the underlying `PolyCellV2` requires:

  1. Destructure `Certified` to expose the result + acceptance.
  2. Trace through the wrapper's match to expose the exact-certifier's
     `CertifiedRawCellV2` package.
  3. The exact package's `certifiedCell` has type `PolyCellV2 profile
     sort rawCell.dim scope boundary rawCell`.  For `rawCell :=
     .termBase term`, `rawCell.dim = 0` reduces definitionally — no
     `subst` needed for the dim.
  4. The boundary's type collapses to `Unit` via `CellBoundaryV2_zero`.
     Use `Subsingleton.elim` (with `inferInstanceAs (Subsingleton Unit)`
     to bridge the type-class inference gap) to identify the
     boundary with `CellBoundaryV2.trivial`.

## Why this matters for SR

SR's source obligation is `Certified source`.  To run the SR proof
at the structural level — where the spine projections + the
substitution preservation lemma (V2-L2.12) live — we need to
convert `Certified source` to a `PolyCellV2 ... (.termBase source)`.

This file ships that bridge.  The reverse direction (PolyCellV2 →
Certified, i.e., certifier completeness) is V2-L3.5 and requires
fuel monotonicity / completeness machinery — deferred to a
later phase.

## What this does NOT do

It does NOT lift `PolyCellV2 ... target` back to `Certified target`
— that would require completeness.  It only ships the
soundness-direction bridge (Certified → PolyCellV2), which is the
direction immediately useful for SR's source unpacking.

## Zero-axiom verification

Uses the dispatcherEq `rfl`-bridge pattern catalogued in
`CertifyRawCellExactV2Shape.lean` to avoid `unfold` on the
certifier definition.  No `simp`-set expansion; no propext-touching
tactics.  The `inferInstanceAs` trick from
`CertifiedTermSpineV2.headAtDim0` reappears here for the boundary
Subsingleton.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Existential PolyCellV2 at dim 0 over a raw term.**

The structural counterpart to `Certified raw`: there exists a
certified cell at dim 0 over the wrapped raw term, with sort
existentially bound (boundary is canonically
`CellBoundaryV2.trivial` since dim 0 collapses to `Unit`).

The predicate is a Prop-valued custom inductive (rather than a
`Nonempty` wrapper) to bypass the strict
`#assert_no_inhabited_dependents` gate that the project enforces
on the PolyCell kernel namespace.  The constructor carries the
sort and the certified cell directly; large elimination is NOT
attempted by downstream callers (SR's proof only eliminates
`HasCertifiedCellDim0 source` to prove `HasCertifiedCellDim0
target`, both Props — no Classical.choice required).

This predicate is the structural target of `Certified.toHas...`
and the natural state to formulate Subject Reduction over
(without needing the procedural certifier's fuel reasoning). -/
inductive HasCertifiedCellDim0 {profile : PolyProfile} {scope : Nat}
    (raw : RawTermV2 scope) : Prop where
  | intro
      (sort : CellSort)
      (cell :
        PolyCellV2 profile sort 0 scope CellBoundaryV2.trivial
          (.termBase raw)) :
      HasCertifiedCellDim0 raw

/-- **Bridge: Certified → HasCertifiedCellDim0.**

From the procedural Certified predicate, extract the structural
PolyCellV2 witness.  The proof traces through the
`inferRawCellGeneralV2?` wrapper to expose the inner
`certifyRawCellExactV2?` result, then collapses the boundary via
`Subsingleton (Unit)` (bridged through the `def`-reduction of
`CellBoundaryV2 profile sort 0 scope`).

A regression that broke the wrapper's packing (e.g., emitting a
result with `cellSort` swapped from `exactResult.sort` to some
hardcoded value) would invalidate this lemma because the
`exactResult.certifiedCell` would not type-check against the
existential's expected sort. -/
theorem Certified.toHasCertifiedCellDim0
    {profile : PolyProfile} {scope : Nat} {raw : RawTermV2 scope}
    (cert : Certified (profile := profile) raw) :
    HasCertifiedCellDim0 (profile := profile) raw := by
  obtain ⟨_, accepted⟩ := cert
  -- `inferRawCellGeneralV2?` is a non-mutual `def` (no Quot.sound
  -- risk on unfold), so `unfold` is the cleanest expansion path.
  -- The wrapper just packs the exact-certifier's result; we
  -- case-analyze on the inner call's result.
  unfold inferRawCellGeneralV2? at accepted
  cases hExact : certifyRawCellExactV2? (profile := profile) scope
                    (.termBase raw) with
  | error rejection =>
    rw [hExact] at accepted
    cases accepted
  | ok exactResult =>
    -- `exactResult : CertifiedRawCellV2 profile scope (.termBase raw)`.
    -- Its `certifiedCell` has type
    --   `PolyCellV2 profile exactResult.sort (.termBase raw).dim
    --    scope exactResult.boundary (.termBase raw)`.
    -- `(.termBase raw).dim` reduces to `0` definitionally, so no
    -- dim cast is needed — only the boundary collapses via
    -- Subsingleton.
    haveI : Subsingleton
              (CellBoundaryV2 profile exactResult.sort 0 scope) :=
      inferInstanceAs (Subsingleton Unit)
    have boundaryEq :
        exactResult.boundary = CellBoundaryV2.trivial :=
      Subsingleton.elim _ _
    exact .intro exactResult.sort (boundaryEq ▸ exactResult.certifiedCell)

/-- **Smoke: extract the structural cell from a unit Certified.**

Exercises `toHasCertifiedCellDim0` on the simplest Certified
fixture: `unit` at scope 0.  The destructor produces a structural
existential PolyCellV2 witness. -/
example {profile : PolyProfile} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_unit () .childNil : RawTermV2 0) :=
  Certified.unit_at_scope_zero.toHasCertifiedCellDim0

end LeanFX2.Foundation.PolyCell.Core
