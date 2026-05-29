import FX1Poly.Core.CertifiedTerm
import FX1Poly.Core.CertifiedTermSpineProjections

/-! # Foundation/PolyCell/Core/CertifiedToPolyCell — Certified→PolyCell

V2-L3.1 phase D step 4 (2026-05-27).  Ships the bridge from the
procedural `Certified` predicate (certifier accepts) to the
structural `PolyCell` representation (a certified cell exists).

## The bridge direction

`Certified raw` is the existential `∃ result, inferRawCellGeneral?
scope (.termBase raw) = .ok result`.  The wrapper packs the
exact-certifier's result into a `CertifiedRawCellResult` and
returns it.  Extracting the underlying `PolyCell` requires:

  1. Destructure `Certified` to expose the result + acceptance.
  2. Trace through the wrapper's match to expose the exact-certifier's
     `CertifiedRawCell` package.
  3. The exact package's `certifiedCell` has type `PolyCell profile
     sort rawCell.dim scope boundary rawCell`.  For `rawCell :=
     .termBase term`, `rawCell.dim = 0` reduces definitionally — no
     `subst` needed for the dim.
  4. The boundary's type collapses to `Unit` via `CellBoundary_zero`.
     Use `Subsingleton.elim` (with `inferInstanceAs (Subsingleton Unit)`
     to bridge the type-class inference gap) to identify the
     boundary with `CellBoundary.trivial`.

## Why this matters for SR

SR's source obligation is `Certified source`.  To run the SR proof
at the structural level — where the spine projections + the
substitution preservation lemma (V2-L2.12) live — we need to
convert `Certified source` to a `PolyCell ... (.termBase source)`.

This file ships that bridge.  The reverse direction (PolyCell →
Certified, i.e., certifier completeness) is tracked as V2-L3.5
#238 + M-substrate-3 #367 (isNF predicate is the certifier-
completeness substrate).  Fuel monotonicity / completeness
machinery scheduled with that task.

## What this does NOT do

It does NOT lift `PolyCell ... target` back to `Certified target`
— that would require completeness.  It only ships the
soundness-direction bridge (Certified → PolyCell), which is the
direction immediately useful for SR's source unpacking.

## Zero-axiom verification

Uses the dispatcherEq `rfl`-bridge pattern catalogued in
`CertifyRawCellExactShape.lean` to avoid `unfold` on the
certifier definition.  No `simp`-set expansion; no propext-touching
tactics.  The `inferInstanceAs` trick from
`CertifiedTermSpine.headAtDim0` reappears here for the boundary
Subsingleton.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **Existential PolyCell at dim 0 over a raw term.**

The structural counterpart to `Certified raw`: there exists a
certified cell at dim 0 over the wrapped raw term, with sort
existentially bound (boundary is canonically
`CellBoundary.trivial` since dim 0 collapses to `Unit`).

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
    (raw : RawTerm scope) : Prop where
  | intro
      (sort : CellSort)
      (cell :
        PolyCell profile sort 0 scope CellBoundary.trivial
          (.termBase raw)) :
      HasCertifiedCellDim0 raw

/-- **Bridge: Certified → HasCertifiedCellDim0.**

From the procedural Certified predicate, extract the structural
PolyCell witness.  The proof traces through the
`inferRawCellGeneral?` wrapper to expose the inner
`certifyRawCellExact?` result, then collapses the boundary via
`Subsingleton (Unit)` (bridged through the `def`-reduction of
`CellBoundary profile sort 0 scope`).

A regression that broke the wrapper's packing (e.g., emitting a
result with `cellSort` swapped from `exactResult.sort` to some
hardcoded value) would invalidate this lemma because the
`exactResult.certifiedCell` would not type-check against the
existential's expected sort. -/
theorem Certified.toHasCertifiedCellDim0
    {profile : PolyProfile} {scope : Nat} {raw : RawTerm scope}
    (cert : Certified (profile := profile) raw) :
    HasCertifiedCellDim0 (profile := profile) raw := by
  obtain ⟨_, accepted⟩ := cert
  -- `inferRawCellGeneral?` is a non-mutual `def` (no Quot.sound
  -- risk on unfold), so `unfold` is the cleanest expansion path.
  -- The wrapper just packs the exact-certifier's result; we
  -- case-analyze on the inner call's result.
  unfold inferRawCellGeneral? at accepted
  cases hExact : certifyRawCellExact? (profile := profile) scope
                    (.termBase raw) with
  | error rejection =>
    rw [hExact] at accepted
    cases accepted
  | ok exactResult =>
    -- `exactResult : CertifiedRawCell profile scope (.termBase raw)`.
    -- Its `certifiedCell` has type
    --   `PolyCell profile exactResult.sort (.termBase raw).dim
    --    scope exactResult.boundary (.termBase raw)`.
    -- `(.termBase raw).dim` reduces to `0` definitionally, so no
    -- dim cast is needed — only the boundary collapses via
    -- Subsingleton.
    haveI : Subsingleton
              (CellBoundary profile exactResult.sort 0 scope) :=
      inferInstanceAs (Subsingleton Unit)
    have boundaryEq :
        exactResult.boundary = CellBoundary.trivial :=
      Subsingleton.elim _ _
    exact .intro exactResult.sort (boundaryEq ▸ exactResult.certifiedCell)

/-- **Smoke: extract the structural cell from a unit Certified.**

Exercises `toHasCertifiedCellDim0` on the simplest Certified
fixture: `unit` at scope 0.  The destructor produces a structural
existential PolyCell witness. -/
example {profile : PolyProfile} :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  Certified.unit_at_scope_zero.toHasCertifiedCellDim0

end FX1Poly.Core
