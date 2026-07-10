import FX1Poly.Polygraph.Computad.Signature

/-! # Polygraph/Omega/Carrier — the dimension-indexed free omega-cell carrier (OMEGA-1 r1, B1)

The prime directive of the omega staircase: **the dimension index is a PARAMETER, never a reason for a
parallel structure**.  `RawTwoCellExpr` (`FreeTwoCell/Model.lean`) is the dim-2 free-cell carrier; this file
lifts its exact idiom to every dimension at once.

## The candidate-ii encoding (Nat-recursion over a prior type, NOT a mutual index)

`CellExpr computad : Nat -> Type` is a single inductive family **indexed by `Nat` only**.  An `(n+1)`-cell is
built OVER the `n`-cells (`CellExpr computad n`) as a completed PRIOR type — exactly as `RawTwoCellExpr` is
built over `ModalityPath` — and its boundary is recovered by TOTAL STRUCTURAL functions
`boundarySource` / `boundaryTarget : CellExpr computad (n+1) -> CellExpr computad n`.  Globularity
(`ss = ts`, `tt = st`) is EXTRINSIC (a `Prop` the computad may or may not satisfy — the `gen` constructor
admits non-globular generators, so it is a stated property, not a theorem; see `IsGlobularCarrier`).

The BANNED alternative (candidate i) indexes cells by a parallel boundary PAIR
(`CellExpr : (n : Nat) -> CellExpr (n-1) -> CellExpr (n-1) -> Type`); that index mentions `CellExpr` and fires
the mutual-index / positivity minefield.  Here the index is `Nat`, a fixed prior type, so no mutual index
arises.

## The five constructors at every dimension (reproducing the dim-2 five on the nose)

`RawTwoCellExpr` has exactly five generators (`gen / id / vcomp / whiskerLeft / whiskerRight`).  `CellExpr`
carries the SAME five, dimension-generically, plus the dim-0 base `ofMode`:

  * `ofMode`       — a 0-cell (a mode).
  * `gen`          — a generating `(n+1)`-cell, its declared source/target `n`-cells carried as fields.
  * `id`           — the identity `(n+1)`-cell on an `n`-cell.
  * `vcomp`        — vertical composition of parallel `(n+1)`-cells (codimension-0 composite).
  * `whiskerLeft`  — precompose an `(n+2)`-cell by an `(n+1)`-cell (codimension-1 whisker).
  * `whiskerRight` — postcompose an `(n+2)`-cell by an `(n+1)`-cell.

Specialised to dimension 2 the constructor set is exactly `{gen, id, vcomp, whiskerLeft, whiskerRight}` — the
five of `RawTwoCellExpr`.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`OmegaComputad`** — the generating data: a mode carrier plus a per-dimension generator-label family.
  * **`CellExpr`** — the dimension-indexed free-cell carrier.
  * **`cellSize`** — the structural size measure (mirrors `RawTwoCellExpr.size`; constant `Nat` motive).
  * **`boundarySource` / `boundaryTarget`** — the total structural boundaries; the whisker boundary is the
    formal `vcomp` (mirroring `RawTwoCellExpr`'s `composePath` boundary, kept inside the five generators).
  * **`IsGlobularCarrier`** — the globularity STATEMENT (`ss = ts`, `tt = st`), a property of a computad's
    generators, not a theorem (the free `gen` constructor admits non-globular generators).

Raw Lean 4 + Init only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The generating data of an omega-computad -/

/-- An **omega-computad** — the generating data of the free omega-category carrier: the 0-cells (`modeCarrier`)
and, for each dimension, a `Type` of generator LABELS (`genLabel`).  A generating `(dim+1)`-cell draws its label
from `genLabel (dim + 1)` and carries its declared source/target `dim`-cells separately (globularity extrinsic),
so `genLabel` need not know the cells its labels span.  This is the untyped / flat presentation the whole
propext-clean substrate follows. -/
structure OmegaComputad where
  /-- The 0-cells (modes) — the base of the dimension tower. -/
  modeCarrier : Type
  /-- The generating cell labels at each dimension: `genLabel d` labels the `d`-cell generators. -/
  genLabel : Nat → Type

/-! ## The dimension-indexed free-cell carrier -/

/-- The **dimension-indexed free omega-cell carrier**.  `CellExpr computad dim` is the type of `dim`-cell
EXPRESSIONS over the computad, indexed by `Nat` (never by a boundary pair — candidate ii).  `CellExpr
computad 0` is the modes; `CellExpr computad (dim+1)` is the free `(dim+1)`-cells over the prior `dim`-cells,
with the five dimension-generic generators.  Specialised to `dim = 2` this reproduces the five constructors of
`RawTwoCellExpr`. -/
inductive CellExpr (computad : OmegaComputad) : Nat → Type where
  /-- A 0-cell: embed a mode. -/
  | ofMode : computad.modeCarrier → CellExpr computad 0
  /-- A generating `(dim+1)`-cell: a label together with its declared source and target `dim`-cells (the
  declared boundary — globularity extrinsic). -/
  | gen {dim : Nat} : computad.genLabel (dim + 1) →
      (source target : CellExpr computad dim) → CellExpr computad (dim + 1)
  /-- The identity `(dim+1)`-cell on a `dim`-cell. -/
  | id {dim : Nat} : CellExpr computad dim → CellExpr computad (dim + 1)
  /-- Vertical composition of two parallel `(dim+1)`-cells (composability extrinsic). -/
  | vcomp {dim : Nat} : CellExpr computad (dim + 1) → CellExpr computad (dim + 1) →
      CellExpr computad (dim + 1)
  /-- Left whiskering: precompose an `(dim+2)`-cell by an `(dim+1)`-cell. -/
  | whiskerLeft {dim : Nat} : CellExpr computad (dim + 1) → CellExpr computad (dim + 2) →
      CellExpr computad (dim + 2)
  /-- Right whiskering: postcompose an `(dim+2)`-cell by an `(dim+1)`-cell. -/
  | whiskerRight {dim : Nat} : CellExpr computad (dim + 2) → CellExpr computad (dim + 1) →
      CellExpr computad (dim + 2)

/-! ## The structural size measure -/

/-- The **structural size** of a cell expression — every generator counts one, composites add their factors
(mirrors `RawTwoCellExpr.size`).  Constant `Nat` motive: the recursor is propext-free. -/
def cellSize {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → Nat
  | _, .ofMode _ => 1
  | _, .gen _ _ _ => 1
  | _, .id _ => 1
  | _, .vcomp left right => cellSize left + cellSize right + 1
  | _, .whiskerLeft _ cell => cellSize cell + 1
  | _, .whiskerRight cell _ => cellSize cell + 1

/-! ## The total structural boundaries

A boundary is a dependent function `CellExpr computad (dim+1) -> CellExpr computad dim`.  A PARTIAL match on
the indexed family (omitting the `ofMode` 0-cell) forces the equation compiler to discharge the impossible
`ofMode`-at-`(dim+1)` case, which drags `propext` / `Quot.sound` (the indexed-partial-match trap).  The clean
route is a TOTAL match over all six constructors into a dependent motive `boundaryMotive` that is `PUnit` at
dimension 0 (where no boundary exists) and `CellExpr computad k` at `k+1`; the public boundary is the wrapper
that reads off the motive at a successor dimension.  Both the worker and the wrapper are zero-axiom. -/

/-- The **boundary motive**: `PUnit` at dimension 0 (a 0-cell has no boundary), `CellExpr computad k` at
`k+1`.  A `Nat`-recursive `Type`, matched inside the total boundary workers so no impossible-case discharge
arises. -/
def boundaryMotive (computad : OmegaComputad) : Nat → Type
  | 0 => PUnit
  | k + 1 => CellExpr computad k

/-- The **total source-boundary worker** — a total match over all six constructors into `boundaryMotive`
(the `ofMode` 0-cell returns the trivial `PUnit.unit`).  Whisker cells return the formal `vcomp` of the
whiskering cell with the recursive boundary (mirroring `RawTwoCellExpr`'s `composePath` boundary, kept inside
the five generators). -/
def boundarySourceTotal {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → boundaryMotive computad dim
  | _, .ofMode _ => PUnit.unit
  | _, .gen _ source _ => source
  | _, .id cell => cell
  | _, .vcomp left _ => boundarySourceTotal left
  | _, .whiskerLeft whiskeringCell cell => CellExpr.vcomp whiskeringCell (boundarySourceTotal cell)
  | _, .whiskerRight cell whiskeringCell => CellExpr.vcomp (boundarySourceTotal cell) whiskeringCell

/-- The **total target-boundary worker** — the dual of `boundarySourceTotal`. -/
def boundaryTargetTotal {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → boundaryMotive computad dim
  | _, .ofMode _ => PUnit.unit
  | _, .gen _ _ target => target
  | _, .id cell => cell
  | _, .vcomp _ right => boundaryTargetTotal right
  | _, .whiskerLeft whiskeringCell cell => CellExpr.vcomp whiskeringCell (boundaryTargetTotal cell)
  | _, .whiskerRight cell whiskeringCell => CellExpr.vcomp (boundaryTargetTotal cell) whiskeringCell

/-- The **source boundary** of an `(dim+1)`-cell — a total structural `dim`-cell, read off
`boundarySourceTotal` at a successor dimension (where `boundaryMotive computad (dim+1)` is definitionally
`CellExpr computad dim`).  Zero-axiom. -/
def boundarySource {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) : CellExpr computad dim :=
  boundarySourceTotal cell

/-- The **target boundary** of an `(dim+1)`-cell — the total structural `dim`-cell dual to `boundarySource`. -/
def boundaryTarget {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) : CellExpr computad dim :=
  boundaryTargetTotal cell

/-! ## Globularity — a STATED property, not a theorem -/

/-- Whether a computad's carrier is **globular**: every `(dim+2)`-cell has a well-defined `dim`-boundary
(`ss = ts` and `tt = st`).  This is STATED, not proven: the free `gen` constructor admits generators whose
declared source and target `(dim+1)`-cells have DIFFERENT `dim`-boundaries, so strict globularity holds only
for computads whose generators are themselves globular.  For whisker / id / vcomp cells it propagates
inductively; the `gen` obligation is the r2 / stratified-carriers handoff.  `IsGlobularCarrier` is the property
a `GlobularComputad` refinement would carry. -/
def IsGlobularCarrier (computad : OmegaComputad) : Prop :=
  ∀ {dim : Nat} (cell : CellExpr computad (dim + 2)),
    boundarySource (boundarySource cell) = boundarySource (boundaryTarget cell) ∧
    boundaryTarget (boundaryTarget cell) = boundaryTarget (boundarySource cell)

/-! ## Structural equality — the flat-skeleton route (propext-clean)

A structural equality on the `Nat`-indexed `CellExpr` cannot pair-match the two cells directly: the offset
whisker constructors (`whiskerLeft` / `whiskerRight` at index `+2`) coexist with `gen` / `id` / `vcomp` (index
`+1`) only above dimension 1, and the equation compiler's index-compatibility reasoning drags `propext` even
under a full constructor enumeration (the indexed-pair-match trap).  The clean route erases the index: flatten
each cell to a NON-indexed `CellSkeleton` by a constant-motive fold (`toSkeleton`, propext-free like
`cellSize`), then compare skeletons with a full-enumeration `Bool` match (no wildcard).  `cellBeq` composes the
two.  Both are zero-axiom; the non-vacuity evals witness `false` on distinct and `true` on equal cells. -/

/-- The **flat cell skeleton** — a NON-indexed mirror of `CellExpr` with the `Nat` index erased (the label
dimension is kept as a field on `genNode`).  Structural equality of `CellExpr` factors through skeleton
equality, dodging the indexed-pair-match propext trap. -/
inductive CellSkeleton (computad : OmegaComputad) where
  /-- A 0-cell leaf. -/
  | modeLeaf : computad.modeCarrier → CellSkeleton computad
  /-- A generator node: its label dimension, its label, and the flattened source / target. -/
  | genNode : (labelDim : Nat) → computad.genLabel labelDim →
      CellSkeleton computad → CellSkeleton computad → CellSkeleton computad
  /-- An identity node. -/
  | idNode : CellSkeleton computad → CellSkeleton computad
  /-- A vertical-composite node. -/
  | vcompNode : CellSkeleton computad → CellSkeleton computad → CellSkeleton computad
  /-- A left-whisker node. -/
  | whiskerLeftNode : CellSkeleton computad → CellSkeleton computad → CellSkeleton computad
  /-- A right-whisker node. -/
  | whiskerRightNode : CellSkeleton computad → CellSkeleton computad → CellSkeleton computad

/-- **Flatten** a cell to its skeleton — a constant-motive structural fold, propext-free (like `cellSize`). -/
def toSkeleton {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → CellSkeleton computad
  | _, .ofMode mode => .modeLeaf mode
  | _, .gen (dim := labelDim) label source target =>
      .genNode (labelDim + 1) label (toSkeleton source) (toSkeleton target)
  | _, .id cell => .idNode (toSkeleton cell)
  | _, .vcomp left right => .vcompNode (toSkeleton left) (toSkeleton right)
  | _, .whiskerLeft whiskeringCell cell =>
      .whiskerLeftNode (toSkeleton whiskeringCell) (toSkeleton cell)
  | _, .whiskerRight cell whiskeringCell =>
      .whiskerRightNode (toSkeleton cell) (toSkeleton whiskeringCell)

/-- Structural **`Bool` equality of skeletons**, parameterised by a mode comparator and a HETEROGENEOUS
generator-label comparator (the label dimensions may differ across two `genNode`s; the caller decides how to
compare, e.g. reject unequal dimensions).  Full constructor enumeration — no wildcard, so propext-free. -/
def skeletonBeq {computad : OmegaComputad}
    (modeBeq : computad.modeCarrier → computad.modeCarrier → Bool)
    (genBeqHetero : (dimA dimB : Nat) → computad.genLabel dimA → computad.genLabel dimB → Bool) :
    CellSkeleton computad → CellSkeleton computad → Bool
  | .modeLeaf modeA, .modeLeaf modeB => modeBeq modeA modeB
  | .genNode dimA labelA sourceA targetA, .genNode dimB labelB sourceB targetB =>
      genBeqHetero dimA dimB labelA labelB
        && skeletonBeq modeBeq genBeqHetero sourceA sourceB
        && skeletonBeq modeBeq genBeqHetero targetA targetB
  | .idNode cellA, .idNode cellB => skeletonBeq modeBeq genBeqHetero cellA cellB
  | .vcompNode leftA rightA, .vcompNode leftB rightB =>
      skeletonBeq modeBeq genBeqHetero leftA leftB && skeletonBeq modeBeq genBeqHetero rightA rightB
  | .whiskerLeftNode whiskerA cellA, .whiskerLeftNode whiskerB cellB =>
      skeletonBeq modeBeq genBeqHetero whiskerA whiskerB && skeletonBeq modeBeq genBeqHetero cellA cellB
  | .whiskerRightNode cellA whiskerA, .whiskerRightNode cellB whiskerB =>
      skeletonBeq modeBeq genBeqHetero cellA cellB && skeletonBeq modeBeq genBeqHetero whiskerA whiskerB
  | .modeLeaf _, .genNode _ _ _ _ => false
  | .modeLeaf _, .idNode _ => false
  | .modeLeaf _, .vcompNode _ _ => false
  | .modeLeaf _, .whiskerLeftNode _ _ => false
  | .modeLeaf _, .whiskerRightNode _ _ => false
  | .genNode _ _ _ _, .modeLeaf _ => false
  | .genNode _ _ _ _, .idNode _ => false
  | .genNode _ _ _ _, .vcompNode _ _ => false
  | .genNode _ _ _ _, .whiskerLeftNode _ _ => false
  | .genNode _ _ _ _, .whiskerRightNode _ _ => false
  | .idNode _, .modeLeaf _ => false
  | .idNode _, .genNode _ _ _ _ => false
  | .idNode _, .vcompNode _ _ => false
  | .idNode _, .whiskerLeftNode _ _ => false
  | .idNode _, .whiskerRightNode _ _ => false
  | .vcompNode _ _, .modeLeaf _ => false
  | .vcompNode _ _, .genNode _ _ _ _ => false
  | .vcompNode _ _, .idNode _ => false
  | .vcompNode _ _, .whiskerLeftNode _ _ => false
  | .vcompNode _ _, .whiskerRightNode _ _ => false
  | .whiskerLeftNode _ _, .modeLeaf _ => false
  | .whiskerLeftNode _ _, .genNode _ _ _ _ => false
  | .whiskerLeftNode _ _, .idNode _ => false
  | .whiskerLeftNode _ _, .vcompNode _ _ => false
  | .whiskerLeftNode _ _, .whiskerRightNode _ _ => false
  | .whiskerRightNode _ _, .modeLeaf _ => false
  | .whiskerRightNode _ _, .genNode _ _ _ _ => false
  | .whiskerRightNode _ _, .idNode _ => false
  | .whiskerRightNode _ _, .vcompNode _ _ => false
  | .whiskerRightNode _ _, .whiskerLeftNode _ _ => false

/-- ★ The **hand-rolled structural equality** on `CellExpr` — flatten both cells and compare skeletons.
Propext-free (no derived instance, no indexed pair-match).  Returns `true` exactly on structurally identical
cells (up to the supplied mode / generator comparators); the non-vacuity evals witness both outcomes.  Promoting
this `Bool` decision to a `Prop`-valued `DecidableEq (CellExpr computad dim)` needs `toSkeleton`-injectivity,
which lives in the same indexed-equality territory and is the mechanical r2 follow-up. -/
def cellBeq {computad : OmegaComputad}
    (modeBeq : computad.modeCarrier → computad.modeCarrier → Bool)
    (genBeqHetero : (dimA dimB : Nat) → computad.genLabel dimA → computad.genLabel dimB → Bool)
    {dim : Nat} (cellA cellB : CellExpr computad dim) : Bool :=
  skeletonBeq modeBeq genBeqHetero (toSkeleton cellA) (toSkeleton cellB)

end FX1Poly.Polygraph.Omega
