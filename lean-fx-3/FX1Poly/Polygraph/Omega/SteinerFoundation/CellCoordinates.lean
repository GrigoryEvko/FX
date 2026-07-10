import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex

/-! # FX1Poly/Polygraph/Steiner/CellCoordinates — cell = integer vector; source/target = d-split
    (frontiers.md §3.1, Appendix A.1)

A dimension-`n` cell is a finite integer vector over the dimension-`n` basis.  Source/target are
the NEGATIVE/POSITIVE parts of the boundary matrix-vector product (`d = d- (join) d+`, Steiner).
Composition is vector arithmetic `x *_k y = x + y - sharedBoundary` (§3.1).

## Zero-axiom design decisions
  * The vector is a plain `List Int`; well-shapedness (`HasDimensionShape`) is EXTRINSIC, so the
    cell type is non-indexed and its equality stays structural (see `DecidableCellEq`).
  * The sign split is a STRUCTURAL two-arm match on `Int`'s constructors (`ofNat`/`negSucc`) — no
    order decision procedure, no `propext`.  `negativeClampEntry` returns the MAGNITUDE, so both
    parts land in the positive cone.
  * `addCoordinates`/`negateCoordinates` are self-defined with fully enumerated arms.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Steiner/CellCoordinates.lean`. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-- The coordinate carrier: a finite integer vector. -/
abbrev CellVector := List Int

/-- A Steiner cell: a coordinate vector, shape carried extrinsically (like `IntMatrix`). -/
structure SteinerCell where
  coordinates : CellVector

/-- The cell has the dimension-`dim` shape of `complex` (its length is `basisCount dim`). -/
def SteinerCell.HasDimensionShape
    (complex : AugmentedDirectedComplex) (dim : Nat) (cell : SteinerCell) : Prop :=
  cell.coordinates.length = complex.basisCount dim

/-! ## Vector arithmetic (fully enumerated; equal-length use is exact) -/

def addCoordinates : CellVector → CellVector → CellVector
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | leftEntry :: leftRemaining, rightEntry :: rightRemaining =>
      (leftEntry + rightEntry) :: addCoordinates leftRemaining rightRemaining

def negateCoordinates : CellVector → CellVector
  | [] => []
  | entry :: remaining => (-entry) :: negateCoordinates remaining

def subtractCoordinates (left right : CellVector) : CellVector :=
  addCoordinates left (negateCoordinates right)

/-! ## The positivity split of d — structural on the Int constructors -/

/-- Positive part of one entry: keep `ofNat`, drop `negSucc`. -/
def positiveClampEntry : Int → Int
  | Int.ofNat magnitude => Int.ofNat magnitude
  | Int.negSucc _ => 0

/-- Negative part of one entry, as a MAGNITUDE (so the result lands in the positive cone). -/
def negativeClampEntry : Int → Int
  | Int.ofNat _ => 0
  | Int.negSucc predecessor => Int.ofNat (predecessor + 1)

def mapPositivePart : CellVector → CellVector
  | [] => []
  | entry :: remaining => positiveClampEntry entry :: mapPositivePart remaining

def mapNegativePart : CellVector → CellVector
  | [] => []
  | entry :: remaining => negativeClampEntry entry :: mapNegativePart remaining

/-! ## Source / target / composition -/

/-- `source = d-` : negative part of the boundary of a dimension-`(dim+1)` cell. -/
def sourceOfCell (complex : AugmentedDirectedComplex) (dim : Nat) (cell : SteinerCell) :
    SteinerCell :=
  ⟨mapNegativePart (complex.applyBoundary dim cell.coordinates)⟩

/-- `target = d+` : positive part of the boundary of a dimension-`(dim+1)` cell. -/
def targetOfCell (complex : AugmentedDirectedComplex) (dim : Nat) (cell : SteinerCell) :
    SteinerCell :=
  ⟨mapPositivePart (complex.applyBoundary dim cell.coordinates)⟩

/-- Composition at a dimension: `x *_k y = x + y - sharedBoundary` (§3.1).  The shared
`k`-boundary is supplied explicitly (a same-dimension cell); its GENERAL computation from the ADC
needs the full Steiner cell-table and is deferred (see split). -/
def composeAtDimension
    (leftCell rightCell sharedBoundary : SteinerCell) : SteinerCell :=
  ⟨subtractCoordinates (addCoordinates leftCell.coordinates rightCell.coordinates)
      sharedBoundary.coordinates⟩

end FX1Poly.Polygraph.Steiner
