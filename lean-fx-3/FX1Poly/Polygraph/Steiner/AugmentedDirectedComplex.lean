import FX1Poly.ComputerAlgebra.IntMatrix

/-! # FX1Poly/Polygraph/Steiner/AugmentedDirectedComplex — the finite-basis ADC carrier
    (frontiers.md §3.1, Appendix A.1; [OurCorollary(Steiner04)] / Loubaton Thm 1.2.1.23)

An augmented directed complex over a FINITE per-dimension basis: a graded family of free
ZZ-modules `Cn = ZZ^(basisCount n)` with a boundary matrix `d : C_{n+1} -> C_n`, an augmentation
`eps : C0 -> ZZ`, and the two chain obligations `d d = 0`, `eps d = 0` — stated as INTEGER-MATRIX
PRODUCTS equal to zero.  Finiteness (a `Nat`-valued `basisCount`) is the enabler: the general
strict-omega-cat word problem is undecidable (Novikov-Boone), so the linear-algebra collapse is
gated on the loop-free / free-on-a-polygraph restriction.

## Zero-axiom design decisions
  * Basis is by COUNT (`basisCount : Nat -> Nat`); an atom of dimension `n` is a `Nat` index,
    valid iff `< basisCount n` — extrinsic, matching `IntMatrix`.  No `Fin`, no indexed inductive.
  * Boundary shape is EXTRINSIC (`boundaryHasDimensions` via `IntMatrix.IsRectangular`), never a
    dependent length — every match stays on non-indexed inductives.
  * `d d = 0` and `eps d = 0` are entrywise `Int`-sum obligations; the summation `sumOverIndices`
    and the row dot product `dotProduct` are self-defined with fully enumerated arms.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Steiner/AugmentedDirectedComplex.lean`. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-- Dot product of two integer rows — fully enumerated arms; ragged rows truncate to the shorter
length (rectangularity keeps every real use exact). -/
def dotProduct : IntRow → IntRow → Int
  | [], [] => 0
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | leftEntry :: leftRemaining, rightEntry :: rightRemaining =>
      leftEntry * rightEntry + dotProduct leftRemaining rightRemaining

/-- Finite sum `Sigma_{index < count} summand index` — structural on `count`, no `Fin`, no fold. -/
def sumOverIndices : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | count + 1, summand => sumOverIndices count summand + summand count

/-- **The finite-basis augmented directed complex.**  Later fields quantify over the earlier
`basisCount`/`boundaryMatrix`, so the chain obligations are self-contained (no forward ref). -/
structure AugmentedDirectedComplex where
  /-- The number of dimension-`n` basis atoms. -/
  basisCount     : Nat → Nat
  /-- `d` from dimension `dim + 1` to dimension `dim`, as a `basisCount dim x basisCount (dim+1)`
      integer matrix (rows = dim atoms, columns = dim+1 atoms). -/
  boundaryMatrix : Nat → IntMatrix
  /-- The augmentation `eps : C0 -> ZZ`, a length-`basisCount 0` row. -/
  augmentation   : IntRow
  /-- Every boundary matrix has the declared rectangular shape. -/
  boundaryHasDimensions :
    ∀ dim, (boundaryMatrix dim).IsRectangular (basisCount dim) (basisCount (dim + 1))
  /-- The augmentation row has width `basisCount 0`. -/
  augmentationHasWidth : augmentation.length = basisCount 0
  /-- `d d = 0`: every entry of `boundaryMatrix dim * boundaryMatrix (dim+1)` within the window
      is zero. -/
  boundaryComposesToZero :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < basisCount dim → colIndex < basisCount (dim + 2) →
      sumOverIndices (basisCount (dim + 1)) (fun middleIndex =>
        (boundaryMatrix dim).entryAt rowIndex middleIndex *
        (boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  /-- `eps d = 0`: the augmentation kills every `d0`-boundary. -/
  augmentationComposesToZero :
    ∀ (colIndex : Nat), colIndex < basisCount 1 →
      sumOverIndices (basisCount 0) (fun middleIndex =>
        listGetWithDefault 0 augmentation middleIndex *
        (boundaryMatrix 0).entryAt middleIndex colIndex) = 0

/-- Multiply each matrix row into a column vector (self-defined for controlled equations). -/
def dotEachRowWithVector : List IntRow → IntRow → List Int
  | [], _ => []
  | row :: remainingRows, vector =>
      dotProduct row vector :: dotEachRowWithVector remainingRows vector

/-- Apply `d_dim` to a dimension-`(dim+1)` coordinate vector — the matrix-vector product. -/
def AugmentedDirectedComplex.applyBoundary
    (complex : AugmentedDirectedComplex) (dim : Nat) (coordinates : IntRow) : IntRow :=
  dotEachRowWithVector (complex.boundaryMatrix dim).rows coordinates

/-- A coordinate vector lies in the POSITIVE CONE iff every entry is nonnegative (the
NN-combinations of basis atoms). -/
def IsInPositiveCone : IntRow → Prop
  | [] => True
  | entry :: remaining => (0 : Int) ≤ entry ∧ IsInPositiveCone remaining

end FX1Poly.Polygraph.Steiner
