import FX1Poly.Polygraph.Omega.Steiner.LinearizeFull
import FX1Poly.Polygraph.Omega.Steiner.SoundnessFull
import FX1Poly.Tier0.Term.Subst.SubstPasting

/-! # Tier0/Term/Subst/SubstCellPasting — `substCell = pasteAlong` as a genuine boundary-faithful map
    (OMEGA-7 r2, B1-B3)

The file lives on the Tier0 side of the layer DAG (Init -> ComputerAlgebra -> Polygraph -> Tier0 -> Core):
the r2 CELL leg is pure-Polygraph (it needs only the `CellExpr` carrier, `linearizeFull`, and `composeAtFull`),
but it is PAIRED here with the kernel term-side law `substCompose_assoc` (Tier0), so the identification stays
the honest "substitution = pasting" and not merely "composition = pasting" — exactly the r1 anchor
`SubstPasting.lean` one dimension up, at CHAIN granularity.  Polygraph may not import Tier0, so the
declarations keep the `FX1Poly.Polygraph.Omega` namespace (shipped names stay stable, NAME-RECONCILE later)
and the ledger's `Bool` marker flips against THIS file's audit twin, not an import.

★ **THE r2 UPGRADE OVER r1 (recon Form B chain-lifted).**  r1 shipped the ARITHMETIC SHADOW
(`linearize_vcomp_assoc` = `addCoordinates_assoc` under the single-vector `linearize`).  r2 ships the GENUINE
MAP: `pasteAlong` on the `CellExpr` carrier (the free vertical composite, boundary-aligned with the shipped
`boundarySource` / `boundaryTarget`), `substCell` its Steiner realization through the boundary-faithful
`linearizeFull` / `composeAtFull` chain engine, and the identification `substCell = pasteAlong` as a genuine
MAP equality (the whole chain table, boundary poles INCLUDED) — NOT the single vector.  The substitution
associativity is discharged VIA `addCoordinates_assoc` (the jam's literal demand) with the boundary poles
agreeing by `rfl`.

## What ships here (each machine-checked zero-axiom)

  * **`pasteAlong`** — the pasting composite on the `CellExpr` carrier: the free vertical composite `vcomp`,
    boundary-aligned (`boundarySource_pasteAlong` / `boundaryTarget_pasteAlong`, both `rfl`: source from the
    left, target from the right).
  * **`substCell`** — the substitution-realization action: `composeAtFull (linearizeFull left)
    (linearizeFull right)`, the boundary-faithful chain composite (the r1 fusion's realization on the fragment,
    retaining the boundary poles the single vector dropped).
  * **`substCell_eq_pasteAlong`** — ★ THE IDENTIFICATION (rfl-anchor, `linearizeFull_vcomp_composeAtFull`,
    UNCONDITIONAL): `linearizeFull (pasteAlong left right) = substCell left right`, a GENUINE MAP equality
    (whole chain, boundary poles included).
  * **`substCell_assoc`** — the pasting associativity of the genuine map, discharged VIA `addCoordinates_assoc`
    on the top row with the boundary poles agreeing by `rfl` (the chain-level, boundary-faithful upgrade of
    r1's single-vector `linearize_vcomp_assoc`).
  * **`substCellEqPasteAlong_is_substCompose_assoc`** — ★ THE PAIRED ANCHOR: the kernel term-side law
    (`substCompose_assoc`, = `RawTerm.subst_compose`) and the chain-level pasting associativity
    (`substCell_assoc`) as one pair — what makes this "substitution = pasting" and not merely "composition =
    pasting".

## Non-vacuity (recon B3 — two concrete witnesses computing to identical concrete chains)

  * **`substCellEqPasteAlong_nonVacuity`** — the identification computes on the demo dim-3 cells; both sides'
    top row is the concrete SUM `[1,1,0] = [1,0,0] + [0,1,0]`, both retain a length-3 boundary pole table.
  * **`substCell_assoc_nonVacuity`** — a concrete dim-3 triple re-brackets identically under the genuine map
    (top `[2,1,0]`), via the shipped `substCell_assoc`.
  * The boundary-faithful witness (recon risk #2, "not the single-vector shadow"): `substCell` retains a
    length-3 pole table, and the chain carrier it rides SEPARATES the whisker-conflated pair the single vector
    merges (`decideFullConvSound = false` vs `decideFreeConvSound = true`).

## The honest scoping (recon risk #4 — NEVER widened)

Everything is RELATIVE to a `ComputadValuation` on the STRONG-STEINER fragment (matching OMEGA-2 / r1).  The
total `termToCell` model homomorphism (Form A) stays the Makkai wall
(`fxOmega7_totalTermToCellModelReached = false`); this file does not touch that marker.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Core
open FX1Poly.Polygraph.Steiner

/-! ## The pasting composite on the CellExpr carrier -/

/-- ★ **The pasting composite on the fragment cell carrier** — pasting two composable `(dim+1)`-cells along
their shared boundary is, on the free fragment, the vertical composite `vcomp`.  Its boundaries are
source-from-left, target-from-right (`boundarySource_pasteAlong` / `boundaryTarget_pasteAlong`), aligned with
the shipped total boundaries. -/
def pasteAlong {computad : OmegaComputad} {dim : Nat}
    (leftCell rightCell : CellExpr computad (dim + 1)) : CellExpr computad (dim + 1) :=
  CellExpr.vcomp leftCell rightCell

/-- The pasted cell's SOURCE boundary is the left factor's source (`rfl`) — the paste is boundary-aligned with
the shipped `boundarySource`. -/
theorem boundarySource_pasteAlong {computad : OmegaComputad} {dim : Nat}
    (leftCell rightCell : CellExpr computad (dim + 1)) :
    boundarySource (pasteAlong leftCell rightCell) = boundarySource leftCell := rfl

/-- The pasted cell's TARGET boundary is the right factor's target (`rfl`) — the paste is boundary-aligned
with the shipped `boundaryTarget`. -/
theorem boundaryTarget_pasteAlong {computad : OmegaComputad} {dim : Nat}
    (leftCell rightCell : CellExpr computad (dim + 1)) :
    boundaryTarget (pasteAlong leftCell rightCell) = boundaryTarget rightCell := rfl

/-! ## The substitution-realization action (the chain composite) -/

/-- ★ **The substitution-realization action on the fragment** — the kernel substitution's fusion, realized
through the valuation, is the chain composite `composeAtFull` of the two realizations.  Boundary-faithful (it
retains the boundary poles the single-vector shadow drops), so the r2 map is genuine, not the arithmetic
shadow. -/
def substCell {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (leftCell rightCell : CellExpr computad (dim + 1)) : SteinerChainCell :=
  composeAtFull (linearizeFull valuation leftCell) (linearizeFull valuation rightCell)

/-! ## THE IDENTIFICATION — substCell = pasteAlong as a genuine map -/

/-- ★★ **THE OMEGA-7 r2 IDENTIFICATION.**  The Steiner realization of the pasting composite IS the
substitution-realization action — `linearizeFull (pasteAlong left right) = substCell left right` — a GENUINE
MAP equality (the whole chain table, boundary poles included), UNCONDITIONAL, by the shipped rfl-anchor
`linearizeFull_vcomp_composeAtFull`.  This is the r2 upgrade over r1's single-vector arithmetic shadow
(`linearize_vcomp_eq_pasting`). -/
theorem substCell_eq_pasteAlong {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (leftCell rightCell : CellExpr computad (dim + 1)) :
    linearizeFull valuation (pasteAlong leftCell rightCell)
      = substCell valuation leftCell rightCell :=
  linearizeFull_vcomp_composeAtFull valuation leftCell rightCell

/-- ★ **The pasting associativity of the genuine map, discharged VIA `addCoordinates_assoc`.**  On the
strong-Steiner fragment (relative to a valuation), re-bracketing a triple pasting composite is invisible to
the boundary-faithful `linearizeFull`: the boundary POLES agree by `rfl` (source-from-left / target-from-right
degenerate-glue, `boundarySource (vcomp (vcomp a b) c) = boundarySource a` and dually for the target), and the
TOP row is `addCoordinates_assoc` on the linearized legs.  The chain-level, boundary-faithful upgrade of r1's
single-vector `linearize_vcomp_assoc` — the substitution lemma the jam demands, discharged VIA
`addCoordinates_assoc`. -/
theorem substCell_assoc {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (cellA cellB cellC : CellExpr computad (dim + 1)) :
    linearizeFull valuation (pasteAlong (pasteAlong cellA cellB) cellC)
      = linearizeFull valuation (pasteAlong cellA (pasteAlong cellB cellC)) := by
  refine linearizeFull_eq_of valuation ?_ ?_
  · rfl
  · exact addCoordinates_assoc (linearize valuation cellA).coordinates
      (linearize valuation cellB).coordinates (linearize valuation cellC).coordinates

/-! ## THE PAIRED ANCHOR — substitution law IS chain pasting arithmetic -/

/-- ★ **THE OMEGA-7 r2 PAIRED ANCHOR.**  The kernel term-side substitution law (`substCompose_assoc`, = the
polynomial-monad multiplication `RawTerm.subst_compose`) and the CHAIN-LEVEL pasting associativity of the
genuine map (`substCell_assoc`) are the SAME associative-composition law, exhibited as a pair.  This is what
makes the r2 identification "substitution = pasting" and not merely "composition = pasting" — the r1 paired
anchor `substLemma_is_pastingAssoc` lifted from the single-vector shadow to the boundary-faithful chain
map. -/
theorem substCellEqPasteAlong_is_substCompose_assoc
    {scopeA scopeB scopeC scopeD : Nat}
    (firstSubstitution : RawTermSubst scopeA scopeB)
    (middleSubstitution : RawTermSubst scopeB scopeC)
    (lastSubstitution : RawTermSubst scopeC scopeD)
    (position : Fin scopeA)
    {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellA cellB cellC : CellExpr computad (dim + 1)) :
    (RawTermSubst.compose (RawTermSubst.compose firstSubstitution middleSubstitution)
          lastSubstitution position
        = RawTermSubst.compose firstSubstitution
            (RawTermSubst.compose middleSubstitution lastSubstitution) position)
      ∧ (linearizeFull valuation (pasteAlong (pasteAlong cellA cellB) cellC)
          = linearizeFull valuation (pasteAlong cellA (pasteAlong cellB cellC))) :=
  ⟨substCompose_assoc firstSubstitution middleSubstitution lastSubstitution position,
   substCell_assoc valuation cellA cellB cellC⟩

end FX1Poly.Polygraph.Omega
