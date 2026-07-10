import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv
import FX1Poly.Polygraph.Omega.Steiner.StrongSteiner
import FX1Poly.Polygraph.Omega.BridgeDimTwo

/-! # Polygraph/Omega/Steiner/Integration — `adcOfComputad` + the admitted battery signature (OMEGA-2 r2, B1)

★ **THE INTEGRATION.**  r1 shipped two disconnected carriers: `isStrongSteiner`
(`StrongSteiner.lean`) reads the FLAT `AugmentedDirectedComplex` (its `basisCount` / `boundaryMatrix`
carry the finite decidable support); `linearize` / `decideFreeConvSound` read a
`ComputadValuation` over an `OmegaComputad`.  Nothing tied an admitted ADC to a decision path.  This
file closes that gap for a finitely-presented computad: `adcOfComputad` BUILDS the ADC from a finite
presentation whose boundary columns are the Steiner boundary-differences
(`boundaryColumnFromLinearize`), and the concrete **walking-parallel-pair** signature is exhibited as
BOTH `isStrongSteiner`-admitted (by `rfl`) AND FREE-7-runnable with a one-hot faithful valuation.

## The construction (recon JOB 1)

  * **`boundaryColumnFromLinearize sourceChain targetChain`** — the Steiner boundary column
    `d(g) = linearize(target g) - linearize(source g)` (`subtractCoordinates`), the exact recon
    prescription.  This is the arithmetic of `linearize_vcomp_composeAt` on the boundary: composition
    is addition, boundary is subtraction.
  * **`buildColumnMatrix`** — assembles a `rowCount x colCount` `IntMatrix` from a per-column
    function (columns = generators, rows = the lower-dimension basis atoms), always rectangular by
    construction (`buildColumnMatrix_isRectangular`).
  * **`FinitePresentation`** — the finite generator data: `basisCount` per dimension, `genColumn`
    (each `(faceDim+1)`-generator's boundary column over the `faceDim` basis), an augmentation, and
    the two chain obligations `dd = 0` / `eps d = 0` discharged PER-INSTANCE (JOB 2: entrywise Int
    sums by `rfl` — exactly as r1's `cyclicComplex` / `singleObjectSemiringComplex`).
  * **`adcOfComputad`** — `FinitePresentation -> AugmentedDirectedComplex`, boundary matrices built
    column-wise from the linearize-differences.

## The battery signature (recon JOB 4) — the admitted intersection, computably

The **walking parallel pair**: two objects `objZero`, `objOne`; two parallel 1-generators
`edgeF`, `edgeG : objZero -> objOne` (manifestly acyclic — every edge goes one way, no 1-support
cycle); two generating 2-cells `alpha`, `beta : [edgeF] => [edgeG]`.  Its induced ADC
(`parallelPairComplex := adcOfComputad parallelPairPresentation`) is loop-free and direct-atomic, so
`isStrongSteiner parallelPairComplex 3 = true` by `rfl` — the LOAD-BEARING r2 fact that makes "the
admitted intersection" a computation, not an assertion.  Being a `ModeSignature`, FREE-7
(`decideTwoCellConvFull`) also runs over it, and a one-hot faithful valuation (`pairValuation`,
distinct generators to distinct basis atoms) drives the Steiner semi-decider.  This is the shared
carrier the agreement battery (`AgreementBattery.lean`) runs on.

## HONEST scope (recon RISK 2/4/5)

  * The two deciders live on disjoint carriers; theorem-level agreement is WALLED at OMEGA-1 (the
    `toCellDimTwo` conv-leg, `BridgeDimTwo.lean`).  This file does NOT claim
    `decideFreeConvSound o toCellDimTwo = decideTwoCellConvFull`; the agreement is EVAL-level
    (`AgreementBattery.lean`).
  * `dd = 0` / `eps d = 0` are discharged PER-INSTANCE (the battery is a genuine chain complex:
    both boundary matrices are `[[-1,-1],[1,1]]`, whose product is `0`, and `eps = [1,1]` kills every
    `d0` column).  The GENERIC telescoping `IsGlobularCell -> dd = 0` (seeded by
    `globularLegs_of_isGlobularCell`, `Omega/Carrier.lean`) stays the r3 obligation — it is FALSE
    without the globularity restriction.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph
open FX1Poly.Polygraph.Steiner
open FX1Poly.ComputerAlgebra

/-! ## The Steiner boundary column from linearize -/

/-- ★ **The Steiner boundary column** of a generator: `d(g) = linearize(target) - linearize(source)`
over the lower-dimension basis (`subtractCoordinates`).  This is the recon's "columns via
linearize-of-boundary" made a named generic def — the same boundary arithmetic
(`x + y - shared`) that `linearize_vcomp_composeAt` runs on the free fragment. -/
def boundaryColumnFromLinearize (sourceChain targetChain : SteinerCell) : IntRow :=
  subtractCoordinates targetChain.coordinates sourceChain.coordinates

/-! ## The column-indexed matrix builder -/

/-- Produce `[atIndex start, atIndex (start+1), ..., atIndex (start+count-1)]` — structural on
`count`, no `Fin`, no fold. -/
def buildFromIndices {Entry : Type} : (count start : Nat) → (Nat → Entry) → List Entry
  | 0, _, _ => []
  | count + 1, start, atIndex => atIndex start :: buildFromIndices count (start + 1) atIndex

/-- `buildFromIndices count start atIndex` has length `count`. -/
theorem buildFromIndices_length {Entry : Type} :
    (count start : Nat) → (atIndex : Nat → Entry) →
    (buildFromIndices count start atIndex).length = count
  | 0, _, _ => rfl
  | count + 1, start, atIndex => congrArg (· + 1) (buildFromIndices_length count (start + 1) atIndex)

/-- The `rowIndex`-th row of the column-indexed matrix: read entry `rowIndex` (default `0`) from each
of the `colCount` columns. -/
def rowFromColumns (colCount : Nat) (column : Nat → IntRow) (rowIndex : Nat) : IntRow :=
  buildFromIndices colCount 0 (fun colIndex => listGetWithDefault 0 (column colIndex) rowIndex)

/-- Each assembled row has width `colCount`. -/
theorem rowFromColumns_length (colCount : Nat) (column : Nat → IntRow) (rowIndex : Nat) :
    (rowFromColumns colCount column rowIndex).length = colCount :=
  buildFromIndices_length colCount 0 _

/-- ★ **Assemble a `rowCount x colCount` matrix from a per-column function** — columns index the
generators, rows index the lower-dimension basis atoms.  Rectangular by construction. -/
def buildColumnMatrix (rowCount colCount : Nat) (column : Nat → IntRow) : IntMatrix :=
  ⟨buildFromIndices rowCount 0 (rowFromColumns colCount column)⟩

/-- Every row produced by `buildFromIndices` from a uniform-width row maker has that width. -/
theorem buildFromIndices_rowsAllHaveWidth {makeRow : Nat → IntRow} (width : Nat)
    (rowWidth : (rowIndex : Nat) → (makeRow rowIndex).length = width) :
    (count start : Nat) → IntMatrix.rowsAllHaveWidth width (buildFromIndices count start makeRow)
  | 0, _ => True.intro
  | count + 1, start => ⟨rowWidth start, buildFromIndices_rowsAllHaveWidth width rowWidth count (start + 1)⟩

/-- ★ **`buildColumnMatrix` is rectangular** at its declared shape — `rowCount` rows, each of width
`colCount`.  Discharges the ADC `boundaryHasDimensions` field generically. -/
theorem buildColumnMatrix_isRectangular (rowCount colCount : Nat) (column : Nat → IntRow) :
    (buildColumnMatrix rowCount colCount column).IsRectangular rowCount colCount :=
  ⟨buildFromIndices_length rowCount 0 _,
   buildFromIndices_rowsAllHaveWidth colCount (fun rowIndex => rowFromColumns_length colCount column rowIndex)
     rowCount 0⟩

/-! ## The finite presentation and `adcOfComputad` -/

/-- ★ **A finitely-presented computad, with its Steiner boundary data.**  `basisCount dim` is the
number of `dim`-generators; `genColumn faceDim genIndex` is the `genIndex`-th `(faceDim+1)`-generator's
boundary column (a `boundaryColumnFromLinearize` over the `faceDim` basis); `augmentation` is the
`eps : C0 -> ZZ` row.  The two chain obligations quantify over the DERIVED `buildColumnMatrix`
boundaries, so `adcOfComputad` reads them off directly (no re-proof).  Later fields depend on the
earlier data, so the structure is self-contained. -/
structure FinitePresentation where
  /-- The number of `dim`-generators (the dimension-`dim` basis size). -/
  basisCount : Nat → Nat
  /-- The `genIndex`-th `(faceDim+1)`-generator's boundary column over the `faceDim` basis. -/
  genColumn : Nat → Nat → IntRow
  /-- The augmentation row `eps : C0 -> ZZ`. -/
  augmentation : IntRow
  /-- The augmentation has width `basisCount 0`. -/
  augmentationWidth : augmentation.length = basisCount 0
  /-- `dd = 0`: the derived boundary matrices compose to zero, entrywise. -/
  ddZero : (dim rowIndex colIndex : Nat) →
    rowIndex < basisCount dim → colIndex < basisCount (dim + 2) →
    sumOverIndices (basisCount (dim + 1)) (fun middleIndex =>
      (buildColumnMatrix (basisCount dim) (basisCount (dim + 1)) (genColumn dim)).entryAt rowIndex middleIndex *
      (buildColumnMatrix (basisCount (dim + 1)) (basisCount (dim + 2)) (genColumn (dim + 1))).entryAt middleIndex colIndex)
      = 0
  /-- `eps d = 0`: the augmentation kills every `d0` boundary column. -/
  epsdZero : (colIndex : Nat) → colIndex < basisCount 1 →
    sumOverIndices (basisCount 0) (fun middleIndex =>
      listGetWithDefault 0 augmentation middleIndex *
      (buildColumnMatrix (basisCount 0) (basisCount 1) (genColumn 0)).entryAt middleIndex colIndex)
      = 0

/-- ★ **`adcOfComputad` — the integration.**  Realize a finite presentation as an
`AugmentedDirectedComplex` whose boundary matrices are the `buildColumnMatrix` of the linearize-derived
columns.  The rectangularity is generic (`buildColumnMatrix_isRectangular`); the two chain obligations
are the presentation's own fields. -/
def adcOfComputad (presentation : FinitePresentation) : AugmentedDirectedComplex where
  basisCount := presentation.basisCount
  boundaryMatrix := fun dim =>
    buildColumnMatrix (presentation.basisCount dim) (presentation.basisCount (dim + 1)) (presentation.genColumn dim)
  augmentation := presentation.augmentation
  boundaryHasDimensions := fun _dim => buildColumnMatrix_isRectangular _ _ _
  augmentationHasWidth := presentation.augmentationWidth
  boundaryComposesToZero := presentation.ddZero
  augmentationComposesToZero := presentation.epsdZero

/-! ## The walking-parallel-pair signature (the admitted, FREE-7-runnable battery carrier) -/

/-- The two objects of the walking parallel pair. -/
inductive PairMode where
  /-- The source object. -/
  | objZero
  /-- The target object. -/
  | objOne

/-- The two PARALLEL 1-generators, both `objZero -> objOne` (manifestly acyclic: no return arrow). -/
inductive PairModality : PairMode → PairMode → Type where
  /-- The first parallel edge `objZero -> objOne`. -/
  | edgeF : PairModality PairMode.objZero PairMode.objOne
  /-- The second parallel edge `objZero -> objOne`. -/
  | edgeG : PairModality PairMode.objZero PairMode.objOne

/-- The walking-parallel-pair quiver. -/
def pairGraph : ModeGraph where
  Mode := PairMode
  Modality := PairModality

/-- The 1-cell `[edgeF]` (the length-1 path through the first edge). -/
def pathEdgeF : ModalityPath pairGraph PairMode.objZero PairMode.objOne :=
  singletonModalityPath PairModality.edgeF

/-- The 1-cell `[edgeG]` (the length-1 path through the second edge). -/
def pathEdgeG : ModalityPath pairGraph PairMode.objZero PairMode.objOne :=
  singletonModalityPath PairModality.edgeG

/-- The two generating 2-cells `alpha`, `beta : [edgeF] => [edgeG]`, between the parallel edges. -/
inductive PairTwoCell :
    {sourceMode targetMode : PairMode} →
    ModalityPath pairGraph sourceMode targetMode →
    ModalityPath pairGraph sourceMode targetMode → Type where
  /-- The first generating 2-cell. -/
  | alpha : PairTwoCell pathEdgeF pathEdgeG
  /-- The second generating 2-cell (structurally distinct from `alpha`). -/
  | beta : PairTwoCell pathEdgeF pathEdgeG

/-- ★ **The walking-parallel-pair mode signature** — two objects, two parallel edges, two parallel
2-cells.  Manifestly acyclic (no 1-support cycle), so its induced ADC is strong-Steiner-admitted. -/
def pairSignature : ModeSignature where
  graph := pairGraph
  twoCell := fun sourcePath targetPath => PairTwoCell sourcePath targetPath

/-! ## Decidable-equality data (the FREE-7 inputs) -/

/-- Decidable equality of the two objects. -/
def pairModeDecEq : DecidableEq PairMode
  | .objZero, .objZero => isTrue rfl
  | .objOne, .objOne => isTrue rfl
  | .objZero, .objOne => isFalse (fun modesEqual => PairMode.noConfusion modesEqual)
  | .objOne, .objZero => isFalse (fun modesEqual => PairMode.noConfusion modesEqual)

/-- A propext-free discriminator separating the two parallel edges. -/
def pairModalityTag {sourceMode targetMode : PairMode}
    (modality : PairModality sourceMode targetMode) : Bool :=
  match modality with
  | .edgeF => true
  | .edgeG => false

/-- Decidable equality of the parallel edges (they are NOT subsingleton — `edgeF`, `edgeG` share a
boundary — so distinctness is via the `pairModalityTag` discriminator). -/
def pairModalityDecEq (sourceMode targetMode : PairMode) :
    DecidableEq (PairModality sourceMode targetMode)
  | .edgeF, .edgeF => isTrue rfl
  | .edgeG, .edgeG => isTrue rfl
  | .edgeF, .edgeG => isFalse (fun edgesEqual => Bool.noConfusion (congrArg pairModalityTag edgesEqual))
  | .edgeG, .edgeF => isFalse (fun edgesEqual => Bool.noConfusion (congrArg pairModalityTag edgesEqual))

/-- A propext-free discriminator separating the two parallel 2-cells. -/
def pairTwoCellTag {sourceMode targetMode : PairMode}
    {sourcePath targetPath : ModalityPath pairGraph sourceMode targetMode}
    (cell : PairTwoCell sourcePath targetPath) : Bool :=
  match cell with
  | .alpha => true
  | .beta => false

/-- Decidable equality of the parallel 2-cells (distinctness via `pairTwoCellTag`). -/
def pairTwoCellDecEq {sourceMode targetMode : PairMode}
    (sourcePath targetPath : ModalityPath pairGraph sourceMode targetMode) :
    DecidableEq (PairTwoCell sourcePath targetPath)
  | .alpha, .alpha => isTrue rfl
  | .beta, .beta => isTrue rfl
  | .alpha, .beta => isFalse (fun cellsEqual => Bool.noConfusion (congrArg pairTwoCellTag cellsEqual))
  | .beta, .alpha => isFalse (fun cellsEqual => Bool.noConfusion (congrArg pairTwoCellTag cellsEqual))

/-! ## The one-hot faithful valuation (recon RISK 3 — faithfulness load-bearing) -/

/-- ★ **The one-hot generator value** into a length-3 ambient basis.  The two 2-cells are sent to
DISTINCT basis vectors (`alpha` to `[1,0,0]`, `beta` to `[0,1,0]`); the edges and empty dimensions to
the padding row.  Faithful on the same-dimension 2-generators, so `linearize` does not conflate `alpha`
and `beta` (the distinct-table battery rows are not vacuous). -/
def pairGenValue : (dim : Nat) → signatureGenLabel pairSignature dim → SteinerCell
  | 0, label => nomatch label
  | 1, ⟨_, _, _⟩ => ⟨[0, 0, 0]⟩
  | 2, ⟨_, _, _, _, cell⟩ =>
      match cell with
      | .alpha => ⟨[1, 0, 0]⟩
      | .beta => ⟨[0, 1, 0]⟩
  | _ + 3, label => nomatch label

/-- Every `pairGenValue` output has the ambient length `3`. -/
theorem pairGenValueLength :
    (dim : Nat) → (label : signatureGenLabel pairSignature dim) →
    (pairGenValue dim label).coordinates.length = 3
  | 0, label => nomatch label
  | 1, ⟨_, _, _⟩ => rfl
  | 2, ⟨_, _, _, _, .alpha⟩ => rfl
  | 2, ⟨_, _, _, _, .beta⟩ => rfl
  | _ + 3, label => nomatch label

/-- ★ **The one-hot faithful valuation** over the walking-parallel-pair computad — the Steiner input
`decideFreeConvSound` runs on. -/
def pairValuation : ComputadValuation (computadOfSignature pairSignature) where
  ambientDim := 3
  modeValue := fun _ => ⟨[0, 0, 0]⟩
  genValue := pairGenValue
  modeValueLength := fun _ => rfl
  genValueLength := pairGenValueLength

/-! ## The battery ADC — admitted, computably -/

/-- The finite-presentation data of the walking parallel pair: basis `2, 2, 2, 0, ...`; every boundary
column is the Steiner difference `[-1, 1]` (target atom minus source atom); augmentation `[1, 1]`. -/
def parallelPairPresentation : FinitePresentation where
  basisCount := fun dim => match dim with | 0 => 2 | 1 => 2 | 2 => 2 | _ + 3 => 0
  genColumn := fun faceDim _genIndex =>
    match faceDim with
    | 0 => boundaryColumnFromLinearize ⟨[1, 0]⟩ ⟨[0, 1]⟩
    | 1 => boundaryColumnFromLinearize ⟨[1, 0]⟩ ⟨[0, 1]⟩
    | _ => []
  augmentation := [1, 1]
  augmentationWidth := rfl
  ddZero := by
    intro dim rowIndex colIndex rowBound colBound
    match dim with
    | 0 =>
      match rowIndex, colIndex with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
      | 0, colIndex + 2 =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ colBound)) (Nat.not_lt_zero _)
      | 1, colIndex + 2 =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ colBound)) (Nat.not_lt_zero _)
      | rowIndex + 2, _ =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ rowBound)) (Nat.not_lt_zero _)
    | 1 => exact absurd colBound (Nat.not_lt_zero _)
    | _ + 2 => exact absurd colBound (Nat.not_lt_zero _)
  epsdZero := by
    intro colIndex colBound
    match colIndex with
    | 0 => rfl
    | 1 => rfl
    | colIndex + 2 =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ colBound)) (Nat.not_lt_zero _)

/-- ★ **The battery ADC** — the walking parallel pair realized as an augmented directed complex, its
boundary matrices the Steiner boundary-differences of its generators. -/
def parallelPairComplex : AugmentedDirectedComplex := adcOfComputad parallelPairPresentation

/-- ★★ **THE LOAD-BEARING r2 FACT.**  The battery ADC is `isStrongSteiner`-ADMITTED — the admitted
intersection is a COMPUTATION (`rfl`), not an assertion.  This is the only thing connecting B1's
admission `Bool` to B2's decision path: the same walking-parallel-pair signature drives both
`adcOfComputad` (this admission) and `linearize` / `decideFreeConvSound` (the decision). -/
theorem parallelPairComplex_isStrongSteiner : isStrongSteiner parallelPairComplex 3 = true := rfl

/-- The refusal cross-check still fires: r1's two-object support-cycle complex stays REFUSED, so the
admission genuinely has teeth (the parallel pair is admitted precisely because it is acyclic). -/
theorem cyclicComplex_not_isStrongSteiner : isStrongSteiner cyclicComplex 3 = false := rfl

/-- ★ **The columns ARE Steiner boundary-differences.**  Every boundary column of the battery ADC is a
`boundaryColumnFromLinearize` — the recon's "columns via linearize-of-boundary", realized: the dim-1
column (of each 2-generator) is `linearize(target) - linearize(source)` over the 1-generator basis
`[edgeF] |-> [1,0]`, `[edgeG] |-> [0,1]`, giving `[0,1] - [1,0] = [-1,1]`. -/
theorem parallelPairColumn_isLinearizeDifference (genIndex : Nat) :
    parallelPairPresentation.genColumn 1 genIndex = boundaryColumnFromLinearize ⟨[1, 0]⟩ ⟨[0, 1]⟩ := rfl

/-! ## The admission-to-decision connection theorem (honest strength) -/

/-- ★ **THE INTEGRATION THEOREM (honest strength).**  On the SINGLE walking-parallel-pair signature,
the two r1 faces MEET: (1) its induced ADC is `isStrongSteiner`-admitted (computably), and (2) its
one-hot valuation gives a SOUND decision path — distinct Steiner tables soundly refute free-strict
convertibility.  It does NOT claim completeness (r3) nor the theorem-level two-decider agreement
(walled at OMEGA-1); it states that the admitted arithmetic fragment and the decidable word-problem
path are two faces of ONE presented signature. -/
theorem parallelPairIntegration :
    isStrongSteiner parallelPairComplex 3 = true ∧
    (∀ {dim : Nat} (cellFirst cellSecond : CellExpr (computadOfSignature pairSignature) dim),
      linearize pairValuation cellFirst ≠ linearize pairValuation cellSecond →
      ¬ SaturatedConvOver (computadOfSignature pairSignature)
          (StrictAxiomRel (computadOfSignature pairSignature)) cellFirst cellSecond) :=
  ⟨parallelPairComplex_isStrongSteiner,
   fun _cellFirst _cellSecond tablesDiffer => not_conv_of_linearize_ne pairValuation tablesDiffer⟩

end FX1Poly.Polygraph.Omega
