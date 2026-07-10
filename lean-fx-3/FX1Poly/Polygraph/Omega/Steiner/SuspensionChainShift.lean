import FX1Poly.Polygraph.Omega.Suspension
import FX1Poly.Polygraph.Omega.Steiner.LinearizeFull

/-! # Polygraph/Omega/Steiner/SuspensionChainShift — the suspension shift lemma (OMEGA-3 r2, B4)

★ **How the boundary-faithful chain table shifts under suspension.**  OMEGA-3 r1 showed the SINGLE vector
is INVARIANT under suspension (`linearize_suspend`, `suspendTable = id`).  At CHAIN granularity the pole
count rises `dim → dim+1` (`polesOf_length`), so `linearizeFull` is NOT invariant: suspension APPENDS one
extra degenerate BOTTOM pole `(zeroVector, zeroVector)` — the `⊥ → ⊤` object-suspension pole — while every
upper pole shifts to the suspended copy of the original (coordinate-identical, since `linearize` is
suspension-invariant).

  * **`appendBottomPole`** — the cons-only "append one bottom pole" helper (no `List.append`, propext-clean).
  * **`polesOf_suspend`** — `polesOf (suspendValuation v) (suspendCell a) = appendBottomPole ambient (polesOf
    v a)`, by structural `Nat`-dimension induction over the boundary recursion (`suspendCell_boundarySource`
    + `linearize_suspend` per pole; the dimension-0 base is the single degenerate bottom pole).
  * **`linearizeFull_suspend`** — the full-table shift: the top is invariant (`linearize_suspend`), the poles
    shift by `appendBottomPole`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The append-one-bottom-pole helper (cons-only, propext-clean) -/

/-- Append ONE degenerate bottom pole `(zeroVector, zeroVector)` at the END of a pole table — cons-only (no
`List.append`), so propext-clean like `addPoleTable`. -/
def appendBottomPole (ambient : Nat) :
    List (CellVector × CellVector) → List (CellVector × CellVector)
  | [] => [(zeroVector ambient, zeroVector ambient)]
  | pole :: rest => pole :: appendBottomPole ambient rest

/-- `appendBottomPole` raises the length by one. -/
theorem appendBottomPole_length (ambient : Nat) :
    (table : List (CellVector × CellVector)) → (appendBottomPole ambient table).length = table.length + 1
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (appendBottomPole_length ambient rest)

/-! ## The pole-table shift under suspension -/

/-- ★ **THE SUSPENSION POLE SHIFT.**  Suspension appends one degenerate bottom pole to the pole table:
`polesOf (suspendValuation v) (suspendCell a) = appendBottomPole v.ambientDim (polesOf v a)`.  Structural on
the `Nat` dimension: at dimension 0 the suspended object contributes the single `(zeroVector, zeroVector)`
bottom pole; at a successor the top pole shifts by `suspendCell_boundarySource` + `linearize_suspend`, and
the tail is the inductive hypothesis. -/
theorem polesOf_suspend {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → (cell : CellExpr computad dim) →
    polesOf (suspendValuation valuation) (suspendCell cell)
      = appendBottomPole valuation.ambientDim (polesOf valuation cell)
  | 0, cell => by
      match cell with
      | .ofMode _ => rfl
  | _ + 1, cell => by
      show ((linearize (suspendValuation valuation) (boundarySource (suspendCell cell))).coordinates,
            (linearize (suspendValuation valuation) (boundaryTarget (suspendCell cell))).coordinates)
            :: polesOf (suspendValuation valuation) (boundarySource (suspendCell cell))
        = ((linearize valuation (boundarySource cell)).coordinates,
           (linearize valuation (boundaryTarget cell)).coordinates)
          :: appendBottomPole valuation.ambientDim (polesOf valuation (boundarySource cell))
      rw [← suspendCell_boundarySource cell, ← suspendCell_boundaryTarget cell,
        linearize_suspend valuation (boundarySource cell),
        linearize_suspend valuation (boundaryTarget cell),
        polesOf_suspend valuation (boundarySource cell)]

/-! ## The full-table shift under suspension -/

/-- ★★ **THE SUSPENSION CHAIN-TABLE SHIFT.**  The boundary-faithful chain table of a suspended cell is the
original's table with the top INVARIANT (`linearize_suspend`) and one degenerate bottom pole APPENDED
(`polesOf_suspend`).  The chain-level refinement of the OMEGA-3 r1 fact "`suspendTable` is the identity". -/
theorem linearizeFull_suspend {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cell : CellExpr computad dim) :
    linearizeFull (suspendValuation valuation) (suspendCell cell)
      = { poles := appendBottomPole valuation.ambientDim (polesOf valuation cell)
          top := (linearize valuation cell).coordinates } := by
  show ({ poles := polesOf (suspendValuation valuation) (suspendCell cell),
          top := (linearize (suspendValuation valuation) (suspendCell cell)).coordinates } : SteinerChainCell)
    = { poles := appendBottomPole valuation.ambientDim (polesOf valuation cell),
        top := (linearize valuation cell).coordinates }
  rw [polesOf_suspend valuation cell,
    congrArg SteinerCell.coordinates (linearize_suspend valuation cell)]

/-! ## Non-vacuity — the extra bottom pole computes on a concrete dim-2 cell -/

/-- The suspended dim-3 cell's pole count is one more than the original dim-2 cell's (the appended bottom
pole is real). -/
theorem suspend_polesOf_length_succ :
    (polesOf (suspendValuation demoValuation) (suspendCell demoTwoCell)).length
      = (polesOf demoValuation demoTwoCell).length + 1 := by
  rw [polesOf_suspend demoValuation demoTwoCell, appendBottomPole_length]

end FX1Poly.Polygraph.Omega
