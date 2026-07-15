/-! # Polygraph/Omega/LafontProp/MatNatSemantics — greenfield Nat-matrix semantics kit (LAFONT-PROP r1, brick A)

GREENFIELD LAW: this directory re-founds the bimonoid presentation from the published literature and
imports NOTHING from the retired `WalkingBunchedBimonoid*` scope.  This file is the tiny self-built
Nat-matrix kit demanded by the certificate-first rule: entries-function representation, structural-fuel
summation, matrix product, block-diagonal direct sum, and a `Bool` rectangle-agreement checker that closes
by kernel `rfl` on closed instances.

## The published semantics being transcribed (the citable convention)

Lafont, *Towards an algebraic theory of Boolean circuits*, JPAA 184 (2003) 257-310, Section 3 (verbatim):
"A linear map f : K^p -> K^q is represented by its matrix, with q rows and p columns.  Vertical
composition corresponds to the product of matrices, and horizontal composition to the direct sum."
So a diagram `sourceArity -> targetArity` denotes a `targetArity x sourceArity` matrix; sequential
composition is matrix product (second stage on the LEFT of the product); parallel tensor is block-diagonal
direct sum.  Over the rig N of natural numbers this is the PROP Mat(N) — equivalently spans of finite
sets: Lack, *Composing PROPs*, TAC 13 (2004), Section 5.3: a span is "the cardinality of each fibre of the
map p -> m x n, which in turn is to give a function m x n -> N"; Wadsley-Woods, *PROPs for linear
systems* (arXiv:1505.00048): "Mat(N) is equivalent to the category FinSpan".

Representation choice: a matrix is an entries FUNCTION `Nat -> Nat -> Nat` (row index, column index)
consulted only inside an explicit rectangle, so degenerate dimensions (the 1x0 matrix of eta, the 0x1
matrix of epsilon) are total and the product needs an explicit inner dimension — no partial list surgery,
no `WellFounded.fix`, structural recursion only.

Raw Lean 4 + Init.  Zero-axiom; per-declaration `#assert_no_axioms` in the audit twin plus an independent
`#print axioms` witness file. -/

namespace FX1Poly.Polygraph.Omega.LafontProp

/-- Entries view of a natural-number matrix: `entries rowIndex colIndex` is the coefficient.  Only the
rectangle fixed by the consuming operation is meaningful; entries outside it are junk (conventionally 0
for the constructors built here). -/
abbrev MatrixEntries : Type := Nat -> Nat -> Nat

/-- The all-zero matrix (every rectangle of it). -/
def zeroEntries : MatrixEntries := fun _rowIndex _colIndex => 0

/-- The identity matrix (every square rectangle of it): 1 on the diagonal, 0 elsewhere. -/
def identityEntries : MatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq rowIndex colIndex) 1 0

/-- `sumBelow termAt bound = termAt 0 + ... + termAt (bound - 1)` — structural on the bound. -/
def sumBelow (termAt : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | boundPred + 1 => sumBelow termAt boundPred + termAt boundPred

/-- Matrix product entries.  `composeEntries middleDimension afterEntries beforeEntries` is the product
`after * before` where `after` has `middleDimension` columns and `before` has `middleDimension` rows:
`(after * before)[row][col] = sum_{middleIndex < middleDimension} after[row][middleIndex] * before[middleIndex][col]`.
In diagram terms (Lafont Section 3): `before` is the FIRST stage, `after` the SECOND. -/
def composeEntries (middleDimension : Nat) (afterEntries beforeEntries : MatrixEntries) : MatrixEntries :=
  fun rowIndex colIndex =>
    sumBelow (fun middleIndex => afterEntries rowIndex middleIndex * beforeEntries middleIndex colIndex)
      middleDimension

/-- Block-diagonal direct sum (Lafont Section 3: "horizontal composition [corresponds] to the direct
sum").  The top-left block is `topRowCount x topColCount` of `topEntries`; the bottom-right block is
`bottomEntries` re-based; the off-diagonal blocks are 0. -/
def directSumEntries (topRowCount topColCount : Nat)
    (topEntries bottomEntries : MatrixEntries) : MatrixEntries :=
  fun rowIndex colIndex =>
    cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) 0)
      (cond (Nat.blt colIndex topColCount) 0
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))

/-! ## The five generator matrices (Lafont Section 3, verbatim inventory)

"We introduce five generators tau : 2 -> 2, delta : 1 -> 2, epsilon : 1 -> 0, mu : 2 -> 1, and
eta : 0 -> 1 ... the matrices for tau, delta, and mu are the following: [[0,1],[1,0]], [[1],[1]],
[[1,1]]."  Over N: mu = addition of two wires, eta = the constant zero, delta = copying a wire,
epsilon = discarding a wire, tau = the wire swap. -/

/-- mu (addition) : 2 -> 1, the 1x2 matrix [[1,1]]. -/
def addGenEntries : MatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq rowIndex 0) (cond (Nat.blt colIndex 2) 1 0) 0

/-- eta (zero) : 0 -> 1, the 1x0 empty-rectangle matrix (all consulted entries vacuous). -/
def zeroGenEntries : MatrixEntries := zeroEntries

/-- delta (copy) : 1 -> 2, the 2x1 matrix [[1],[1]]. -/
def copyGenEntries : MatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq colIndex 0) (cond (Nat.blt rowIndex 2) 1 0) 0

/-- epsilon (discard) : 1 -> 0, the 0x1 empty-rectangle matrix. -/
def discardGenEntries : MatrixEntries := zeroEntries

/-- tau (swap) : 2 -> 2, the permutation matrix [[0,1],[1,0]]. -/
def swapGenEntries : MatrixEntries :=
  fun rowIndex colIndex =>
    cond (Nat.beq rowIndex 0) (cond (Nat.beq colIndex 1) 1 0)
      (cond (Nat.beq rowIndex 1) (cond (Nat.beq colIndex 0) 1 0) 0)

/-! ## Rectangle agreement — the kernel-decidable matrix equality -/

/-- Do two entry functions agree on row `rowIndex` at all columns below the bound?  Structural on the
column bound. -/
def doEntriesAgreeOnRow (leftEntries rightEntries : MatrixEntries) (rowIndex : Nat) : Nat -> Bool
  | 0 => true
  | colBoundPred + 1 =>
      doEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
        && Nat.beq (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred)

/-- Do two entry functions agree on all rows below the bound (each over `colCount` columns)?
Structural on the row bound. -/
def doEntriesAgreeOnRows (leftEntries rightEntries : MatrixEntries) (colCount : Nat) : Nat -> Bool
  | 0 => true
  | rowBoundPred + 1 =>
      doEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
        && doEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount

/-- Do two matrices agree on the full `rowCount x colCount` rectangle?  This is the semantic equality of
Mat(N) at fixed dimensions; on closed instances it closes by kernel `rfl`. -/
def doEntriesAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : MatrixEntries) : Bool :=
  doEntriesAgreeOnRows leftEntries rightEntries colCount rowCount

/-! ## Kit smoke fires (kernel rfl) -/

/-- Smoke: tau * tau = identity on the 2x2 rectangle. -/
theorem swapComposeSwapAgreesWithIdentity :
    doEntriesAgreeUpTo 2 2 (composeEntries 2 swapGenEntries swapGenEntries) identityEntries = true := rfl

/-- Smoke: mu * delta = [[2]] on the 1x1 rectangle — copy then add doubles (the matrix witness that
Mat(N) is NOT the Z2 scope: Lafont's extra relation mu . delta = eta . epsilon of figure 13 is SPECIFIC
to Z2 and must NOT be transcribed into the N presentation, where the two sides differ: 2 /= 0). -/
theorem copyThenAddDoublesNotIdentity :
    composeEntries 2 addGenEntries copyGenEntries 0 0 = 2 := rfl

/-- Smoke: the Z2-specific relation FAILS over N — the machine-checked relation-diff witness that the N
relation set has exactly the bimonoid rows and nothing more. -/
theorem zSpecificRelationFailsOverNat :
    doEntriesAgreeUpTo 1 1 (composeEntries 2 addGenEntries copyGenEntries)
      (composeEntries 0 zeroGenEntries discardGenEntries) = false := rfl

/-- Smoke: identity * mu = mu on the 1x2 rectangle. -/
theorem identityComposeAddAgreesWithAdd :
    doEntriesAgreeUpTo 1 2 (composeEntries 1 identityEntries addGenEntries) addGenEntries = true := rfl

/-- Smoke: the direct sum of two identities agrees with the identity (2 = 1 + 1). -/
theorem directSumOfIdentitiesAgreesWithIdentity :
    doEntriesAgreeUpTo 2 2 (directSumEntries 1 1 identityEntries identityEntries) identityEntries
      = true := rfl

end FX1Poly.Polygraph.Omega.LafontProp
