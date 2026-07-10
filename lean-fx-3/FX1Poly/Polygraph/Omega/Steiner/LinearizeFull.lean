import FX1Poly.Polygraph.Omega.Steiner.ChainCell
import FX1Poly.Polygraph.Omega.Steiner.Linearize
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv

/-! # Polygraph/Omega/Steiner/LinearizeFull — the full-chain ν map + the projection tie (OMEGA-2.5 r1, B2)

★ **The boundary-faithful linearize.**  `linearizeFull` sends a free `dim`-cell to its Steiner CHAIN
table `SteinerChainCell` — the top vector PLUS one `(source, target)` pole pair per dimension below.  It
rides the SHIPPED single-vector `linearize` (OMEGA-2, `Linearize.lean`): the top row IS `linearize`, and
each pole row is `linearize` re-run on an iterated total boundary (`boundarySource` / `boundaryTarget`,
`Carrier.lean`).  So no new generator data is needed — the same `ComputadValuation` drives both.

## The projection tie (the load-bearing regression guarantee)

`linearizeFull_top` : `(linearizeFull v cell).top = (linearize v cell).coordinates` — by `rfl`.  The
shipped single vector IS the crown row of the chain table, so `linearize` / `SteinerCell` /
`decideFreeConvSound` / `decideAtomWordConv` all stay LIVE and unchanged; `linearizeFull` is a bridged
SIBLING, a strictly stronger refuter (JOB 3).  No shipped decl is touched.

## The pole recursion (structural on the dimension index, never `WellFounded.fix`)

`polesOf` is a total structural recursion on the `Nat` dimension: dimension 0 has no poles; a
`(dim+1)`-cell prepends its top-adjacent pole `((linearize (boundarySource cell)).coords,
(linearize (boundaryTarget cell)).coords)` to the poles of its `boundarySource` (a `dim`-cell).  The
list is built TOP-FIRST, cons-only (no `List.append`).  `polesOf_length` confirms `(polesOf cell).length
= dim`.

## The four congruence lemmas (the well-behavedness `linearizeFullAbsorbs` consumes)

`linearizeFull_vcompCongrLeft` / `_vcompCongrRight` / `_whiskerLeftCongr` / `_whiskerRightCongr`: from
`linearizeFull a = linearizeFull b` derive the one-hole-context equalities.  These fold cleanly because
`linearizeFull cell` (for a successor cell) is DETERMINED by `linearize cell`, `linearize (bs cell)`,
`linearize (bt cell)`, and `linearizeFull (bs cell)` (the boundary-decomposition helpers) — the whisker
congruences reduce to the `vcomp` congruences through the whisker's formal `vcomp` boundary.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The pole recursion and the full-chain ν map -/

/-- The **boundary poles** of a free `dim`-cell, top-adjacent first: a `(dim+1)`-cell contributes its
top pole `((linearize (boundarySource cell)).coords, (linearize (boundaryTarget cell)).coords)` then
recurses into its `boundarySource` (a `dim`-cell).  Structural on the `Nat` dimension index (the boundary
lowers dimension by one), so total and `WellFounded.fix`-free; cons-only, so propext-clean. -/
def polesOf {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → CellExpr computad dim → List (CellVector × CellVector)
  | 0, _ => []
  | _ + 1, cell =>
      ((linearize valuation (boundarySource cell)).coordinates,
        (linearize valuation (boundaryTarget cell)).coordinates)
        :: polesOf valuation (boundarySource cell)

/-- ★ **The boundary-faithful ν map** `linearizeFull : CellExpr computad dim → SteinerChainCell` — the
top vector is the shipped `linearize`, the poles are `polesOf`.  The SIBLING of `linearize` that records
the boundary context the single vector drops. -/
def linearizeFull {computad : OmegaComputad} (valuation : ComputadValuation computad) {dim : Nat}
    (cell : CellExpr computad dim) : SteinerChainCell where
  poles := polesOf valuation cell
  top := (linearize valuation cell).coordinates

/-! ## The projection tie + the length invariant -/

/-- ★ **THE PROJECTION TIE.**  The chain table's top row IS the shipped single vector — `rfl`.  The
crown-preservation guarantee: `linearize` and its whole decision path stay live and unchanged. -/
theorem linearizeFull_top {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cell : CellExpr computad dim) :
    (linearizeFull valuation cell).top = (linearize valuation cell).coordinates := rfl

/-- The chain table's poles ARE `polesOf` — `rfl`. -/
theorem linearizeFull_poles {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cell : CellExpr computad dim) :
    (linearizeFull valuation cell).poles = polesOf valuation cell := rfl

/-- **The pole count equals the dimension** — `(polesOf cell).length = dim` (the chain-level analog of
`linearize_length`).  Structural on the dimension. -/
theorem polesOf_length {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → (cell : CellExpr computad dim) → (polesOf valuation cell).length = dim
  | 0, _ => rfl
  | _ + 1, cell => congrArg (· + 1) (polesOf_length valuation (boundarySource cell))

/-! ## The reconstruction-from-parts lemma -/

/-- Two chain tables are equal when their poles and their tops agree. -/
theorem linearizeFull_eq_of {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad dim}
    (polesEqual : polesOf valuation leftCell = polesOf valuation rightCell)
    (topEqual : (linearize valuation leftCell).coordinates
      = (linearize valuation rightCell).coordinates) :
    linearizeFull valuation leftCell = linearizeFull valuation rightCell := by
  show (⟨polesOf valuation leftCell, (linearize valuation leftCell).coordinates⟩ : SteinerChainCell)
    = ⟨polesOf valuation rightCell, (linearize valuation rightCell).coordinates⟩
  rw [polesEqual, topEqual]

/-! ## The boundary-decomposition helpers (read `linearizeFull`'s parts off an equality) -/

/-- Read off the top-row equality from a `linearizeFull` equality. -/
theorem linearizeFull_topCoord_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad dim}
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation rightCell) :
    (linearize valuation leftCell).coordinates = (linearize valuation rightCell).coordinates :=
  congrArg SteinerChainCell.top chainEqual

/-- Read off the pole-list equality from a `linearizeFull` equality. -/
theorem linearizeFull_poles_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad dim}
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation rightCell) :
    polesOf valuation leftCell = polesOf valuation rightCell :=
  congrArg SteinerChainCell.poles chainEqual

/-- Read off the SOURCE top-pole equality from a `linearizeFull` equality (a successor cell). -/
theorem linearizeFull_bsCoord_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad (dim + 1)}
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation rightCell) :
    (linearize valuation (boundarySource leftCell)).coordinates
      = (linearize valuation (boundarySource rightCell)).coordinates :=
  congrArg (fun poleList => (List.headD poleList ([], [])).1)
    (linearizeFull_poles_eq valuation chainEqual)

/-- Read off the TARGET top-pole equality from a `linearizeFull` equality (a successor cell). -/
theorem linearizeFull_btCoord_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad (dim + 1)}
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation rightCell) :
    (linearize valuation (boundaryTarget leftCell)).coordinates
      = (linearize valuation (boundaryTarget rightCell)).coordinates :=
  congrArg (fun poleList => (List.headD poleList ([], [])).2)
    (linearizeFull_poles_eq valuation chainEqual)

/-- Read off the `boundarySource` chain-table equality from a `linearizeFull` equality (a successor
cell) — the recursion the whisker congruences chase through their formal `vcomp` boundary. -/
theorem linearizeFull_bs_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad (dim + 1)}
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation rightCell) :
    linearizeFull valuation (boundarySource leftCell)
      = linearizeFull valuation (boundarySource rightCell) := by
  refine linearizeFull_eq_of valuation ?_ (linearizeFull_bsCoord_eq valuation chainEqual)
  exact congrArg List.tail (linearizeFull_poles_eq valuation chainEqual)

/-! ## The successor reconstruction (the congruence-proof engine) -/

/-- Reconstruct a `linearizeFull` equality at a successor dimension from the four pieces: the top row,
the two top-pole rows, and the `boundarySource` chain table. -/
theorem linearizeFull_eq_succ {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell rightCell : CellExpr computad (dim + 1)}
    (topEqual : (linearize valuation leftCell).coordinates
      = (linearize valuation rightCell).coordinates)
    (bsCoordEqual : (linearize valuation (boundarySource leftCell)).coordinates
      = (linearize valuation (boundarySource rightCell)).coordinates)
    (btCoordEqual : (linearize valuation (boundaryTarget leftCell)).coordinates
      = (linearize valuation (boundaryTarget rightCell)).coordinates)
    (bsFullEqual : linearizeFull valuation (boundarySource leftCell)
      = linearizeFull valuation (boundarySource rightCell)) :
    linearizeFull valuation leftCell = linearizeFull valuation rightCell := by
  refine linearizeFull_eq_of valuation ?_ topEqual
  show ((linearize valuation (boundarySource leftCell)).coordinates,
        (linearize valuation (boundaryTarget leftCell)).coordinates)
        :: polesOf valuation (boundarySource leftCell)
    = ((linearize valuation (boundarySource rightCell)).coordinates,
        (linearize valuation (boundaryTarget rightCell)).coordinates)
        :: polesOf valuation (boundarySource rightCell)
  rw [bsCoordEqual, btCoordEqual, linearizeFull_poles_eq valuation bsFullEqual]

/-! ## The four one-hole congruences -/

/-- Congruence in the LEFT factor of a vertical composite. -/
theorem linearizeFull_vcompCongrLeft {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {leftCell leftCell' : CellExpr computad (dim + 1)}
    (rightCell : CellExpr computad (dim + 1))
    (chainEqual : linearizeFull valuation leftCell = linearizeFull valuation leftCell') :
    linearizeFull valuation (CellExpr.vcomp leftCell rightCell)
      = linearizeFull valuation (CellExpr.vcomp leftCell' rightCell) := by
  refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
  · show addCoordinates (linearize valuation leftCell).coordinates (linearize valuation rightCell).coordinates
      = addCoordinates (linearize valuation leftCell').coordinates (linearize valuation rightCell).coordinates
    rw [linearizeFull_topCoord_eq valuation chainEqual]
  · have bsPole := linearizeFull_bsCoord_eq valuation chainEqual
    exact bsPole
  · rfl
  · have bsChain := linearizeFull_bs_eq valuation chainEqual
    exact bsChain

/-- Congruence in the RIGHT factor of a vertical composite. -/
theorem linearizeFull_vcompCongrRight {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} (leftCell : CellExpr computad (dim + 1))
    {rightCell rightCell' : CellExpr computad (dim + 1)}
    (chainEqual : linearizeFull valuation rightCell = linearizeFull valuation rightCell') :
    linearizeFull valuation (CellExpr.vcomp leftCell rightCell)
      = linearizeFull valuation (CellExpr.vcomp leftCell rightCell') := by
  refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
  · show addCoordinates (linearize valuation leftCell).coordinates (linearize valuation rightCell).coordinates
      = addCoordinates (linearize valuation leftCell).coordinates (linearize valuation rightCell').coordinates
    rw [linearizeFull_topCoord_eq valuation chainEqual]
  · rfl
  · have btPole := linearizeFull_btCoord_eq valuation chainEqual
    exact btPole
  · rfl

/-- Congruence under a left whiskering — reduces to `vcompCongrRight` through the whisker's formal
`vcomp` source boundary. -/
theorem linearizeFull_whiskerLeftCongr {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} (whiskeringCell : CellExpr computad (dim + 1))
    {innerCell innerCell' : CellExpr computad (dim + 2)}
    (chainEqual : linearizeFull valuation innerCell = linearizeFull valuation innerCell') :
    linearizeFull valuation (CellExpr.whiskerLeft whiskeringCell innerCell)
      = linearizeFull valuation (CellExpr.whiskerLeft whiskeringCell innerCell') := by
  refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
  · have topRow := linearizeFull_topCoord_eq valuation chainEqual
    exact topRow
  · show addCoordinates (linearize valuation whiskeringCell).coordinates
        (linearize valuation (boundarySource innerCell)).coordinates
      = addCoordinates (linearize valuation whiskeringCell).coordinates
        (linearize valuation (boundarySource innerCell')).coordinates
    rw [linearizeFull_bsCoord_eq valuation chainEqual]
  · show addCoordinates (linearize valuation whiskeringCell).coordinates
        (linearize valuation (boundaryTarget innerCell)).coordinates
      = addCoordinates (linearize valuation whiskeringCell).coordinates
        (linearize valuation (boundaryTarget innerCell')).coordinates
    rw [linearizeFull_btCoord_eq valuation chainEqual]
  · have bsChain := linearizeFull_vcompCongrRight valuation whiskeringCell
      (linearizeFull_bs_eq valuation chainEqual)
    exact bsChain

/-- Congruence under a right whiskering — reduces to `vcompCongrLeft` through the whisker's formal
`vcomp` source boundary. -/
theorem linearizeFull_whiskerRightCongr {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    {innerCell innerCell' : CellExpr computad (dim + 2)}
    (whiskeringCell : CellExpr computad (dim + 1))
    (chainEqual : linearizeFull valuation innerCell = linearizeFull valuation innerCell') :
    linearizeFull valuation (CellExpr.whiskerRight innerCell whiskeringCell)
      = linearizeFull valuation (CellExpr.whiskerRight innerCell' whiskeringCell) := by
  refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
  · have topRow := linearizeFull_topCoord_eq valuation chainEqual
    exact topRow
  · show addCoordinates (linearize valuation (boundarySource innerCell)).coordinates
        (linearize valuation whiskeringCell).coordinates
      = addCoordinates (linearize valuation (boundarySource innerCell')).coordinates
        (linearize valuation whiskeringCell).coordinates
    rw [linearizeFull_bsCoord_eq valuation chainEqual]
  · show addCoordinates (linearize valuation (boundaryTarget innerCell)).coordinates
        (linearize valuation whiskeringCell).coordinates
      = addCoordinates (linearize valuation (boundaryTarget innerCell')).coordinates
        (linearize valuation whiskeringCell).coordinates
    rw [linearizeFull_btCoord_eq valuation chainEqual]
  · have bsChain := linearizeFull_vcompCongrLeft valuation whiskeringCell
      (linearizeFull_bs_eq valuation chainEqual)
    exact bsChain

/-! ## The composeAtFull homomorphism (the B1 op tied to the ν map, UNCONDITIONALLY) -/

/-- ★ **Composition IS the chain composite** — `linearizeFull (vcomp a b) = composeAtFull (linearizeFull
a) (linearizeFull b)`, UNCONDITIONALLY (no composability side condition, no `Option`).  The shared-boundary
crux the recon flagged dissolves: `linearizeFull` reads its lower rows off `boundarySource` directly, and
the top pole is glued `(source from a, target from b)` — exactly `composeAtFull`.  `rfl`. -/
theorem linearizeFull_vcomp_composeAtFull {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (leftCell rightCell : CellExpr computad (dim + 1)) :
    linearizeFull valuation (CellExpr.vcomp leftCell rightCell)
      = composeAtFull (linearizeFull valuation leftCell) (linearizeFull valuation rightCell) := rfl

/-! ## Non-vacuity — the chain table of a demo dim-3 cell computes -/

/-- The full-chain table's TOP row equals the shipped single vector (the projection tie, on a concrete
dim-3 cell): both `[1, 0, 0]`. -/
example : (linearizeFull demoValuation cellThreeA).top = (linearize demoValuation cellThreeA).coordinates := rfl

/-- The pole count of the dim-3 cell equals its dimension. -/
example : (linearizeFull demoValuation cellThreeA).poles.length = 3 := rfl

end FX1Poly.Polygraph.Omega
