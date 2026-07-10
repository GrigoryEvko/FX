import FX1Poly.Polygraph.Omega.StrictAxioms
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # Polygraph/Omega/BridgeDimTwo — the n=2 bridge to `RawTwoCellExpr` as a Prop STATEMENT (OMEGA-1 r1, B4a)

The T1.bridge-n2 deliverable, as a forward-declared proposition (r2 proves it).  The dim-2 free 2-cell carrier
is the shipped `RawTwoCellExpr` (`FreeTwoCell/Model.lean:52`) with five constructors and boundary-as-index; the
generic `CellExpr (computadOfSignature sig) 2` has the SAME five constructors with boundary-as-function.  The
bridge asserts a size-preserving, convertibility-respecting translation between them.

## The falsifiability check (verified structurally, not just stated)

The four one-hole congruence constructors of the generic `SaturatedConvOver` at `dim = 2` — `vcompCongrLeft`,
`vcompCongrRight`, `whiskerLeftCongr`, `whiskerRightCongr` — reproduce the four shipped dim-2 congruence
constructors (`Amalgam/SaturatedOver.lean`) on the nose (their shapes match term-for-term; see
`Omega/Congruence.lean`).  So no parallel structure crept in.  The one honest divergence is `ofFull`: the
generic side has no `TwoCellConvFull` embedding; its content is reproduced by firing `StrictAxiomRel` rows
through `ofRelation`.  Hence the bridge is `{generic ctors + StrictAxiomRel rows} <-> {shipped ctors}`, not a
ctor-for-ctor identity — the free dim-2 convertibility `TwoCellConv` corresponds to the free strict congruence
`freeStrictCongruence emptyPresentation`.

## What r1 ships (statement only)

  * **`computadOfSignature`** — the omega-computad whose dim-1 generators are the signature's modality edges and
    whose dim-2 generators are the signature's generating 2-cells.
  * **`DimTwoTranslation`** — the type of a boundary-forgetting translation `RawTwoCellExpr -> CellExpr .. 2`.
  * **`bridgeDimTwoHolds`** — the forward-declared Prop: SUCH a translation exists that preserves `size` and
    carries `TwoCellConv` into `freeStrictCongruence`.  Defining a Prop introduces no axiom; r2 inhabits it.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph

/-! ## The computad of a mode signature -/

/-- The **generator labels of a mode signature** — modality edges at dimension 1, generating 2-cells at
dimension 2 (each flattened over its boundary data), nothing elsewhere.  A `Nat`-recursive `Type`,
propext-free (mirrors `graphGenLabel`). -/
def signatureGenLabel (signature : ModeSignature) : Nat → Type
  | 1 => Sigma fun (sourceMode : signature.graph.Mode) =>
      Sigma fun (targetMode : signature.graph.Mode) => signature.graph.Modality sourceMode targetMode
  | 2 => Sigma fun (sourceMode : signature.graph.Mode) =>
      Sigma fun (targetMode : signature.graph.Mode) =>
      Sigma fun (sourcePath : ModalityPath signature.graph sourceMode targetMode) =>
      Sigma fun (targetPath : ModalityPath signature.graph sourceMode targetMode) =>
        signature.twoCell sourcePath targetPath
  | 0 => PEmpty
  | _ + 3 => PEmpty

/-- The **omega-computad of a mode signature** — modes as 0-cells, modality edges as dim-1 generators, and the
signature's generating 2-cells as dim-2 generators.  `CellExpr (computadOfSignature signature) 2` is the generic
counterpart of `RawTwoCellExpr signature`. -/
def computadOfSignature (signature : ModeSignature) : OmegaComputad where
  modeCarrier := signature.graph.Mode
  genLabel := signatureGenLabel signature

/-! ## The bridge statement -/

/-- The type of a **boundary-forgetting dim-2 translation** from the shipped free 2-cell carrier to the generic
carrier.  `RawTwoCellExpr` is indexed by a parallel pair of 1-cells; the image forgets that index into the
extrinsic-boundary `CellExpr .. 2` (whose boundary is recovered by `boundarySource` / `boundaryTarget`). -/
def DimTwoTranslation (signature : ModeSignature) : Type :=
  {sourceMode targetMode : signature.graph.Mode} →
  {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
  RawTwoCellExpr signature sourcePath targetPath → CellExpr (computadOfSignature signature) 2

/-- ★ **STATEMENT: the n=2 bridge to `RawTwoCellExpr`.**  There exists a dim-2 translation that (1) preserves
the structural size and (2) carries the free dim-2 convertibility `TwoCellConv` into the free strict congruence
`freeStrictCongruence emptyPresentation` on the generic carrier.  This is the T1.bridge-n2 claim; it is a
forward-declared proposition (defining it introduces no axiom).  **r2 status:** the translation `toCellDimTwo`
and the SIZE leg (1) are PROVEN (`bridgeDimTwoForwardSize`); the CONV leg (2) is the named wall below — the
shipped `freeStrictCongruence` (four one-hole congruences, matching dim-2 exactly) is not a full congruence over
the Omega carrier's EXPLICIT 1-cells, so the `vcompIdLeft` row needs an `id`-congruence it lacks.  This
statement keeps its r1 name and meaning; it is NOT weakened. -/
def bridgeDimTwoHolds (signature : ModeSignature) : Prop :=
  ∃ toCell : DimTwoTranslation signature,
    (∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        (cell : RawTwoCellExpr signature sourcePath targetPath),
        cellSize (toCell cell) = cell.size) ∧
    (∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath},
        TwoCellConv signature cellAlpha cellBeta →
        freeStrictCongruence (computadOfSignature signature)
          (emptyPresentation (computadOfSignature signature)) (toCell cellAlpha) (toCell cellBeta))

/-! ## The bridge translation + the PROVEN forward-size leg (OMEGA-1 r2, B2)

r2 constructs the concrete translation `toCellDimTwo : RawTwoCellExpr → CellExpr .. 2` and PROVES the
size-preservation leg of `bridgeDimTwoHolds` (`bridgeDimTwoForwardSize`).  The five `RawTwoCellExpr` generators
map to the five `CellExpr` generators on the nose (`gen ↦ gen`, `id ↦ id`, `vcomp ↦ vcomp`, `whiskerLeft ↦
whiskerLeft`, `whiskerRight ↦ whiskerRight`), forgetting the boundary index into the extrinsic carrier — the
falsifiability content: the dim-2 instance needs NO extra generator, so no parallel structure crept in.

### The conv-leg wall (named precisely, honest refinement)

The conversion-preservation leg of `bridgeDimTwoHolds` (`TwoCellConv → freeStrictCongruence`) is NOT discharged
this round, and the r1 statement is too strong for the shipped `freeStrictCongruence`.  Reason: `freeStrictCongruence`
closes under the FOUR one-hole congruences (`vcompCongr{Left,Right}`, `whisker{Left,Right}Congr`) that reproduce
the dim-2 congruence exactly — but it is NOT a FULL congruence over the `CellExpr` carrier: it lacks a
DIM-SHIFT `id`-congruence (`a ~_n b → CellExpr.id a ~_{n+1} CellExpr.id b`) and a whiskering-1-cell congruence.
The dim-2 carrier `RawTwoCellExpr` escapes needing these because its 1-cells are the PRE-NORMALISED
`ModalityPath` free monoid; the Omega carrier represents composite 1-cells EXPLICITLY, so
`realizePathCellSig (composePath a b)` is only CONVERTIBLE (not definitionally equal) to
`CellExpr.vcomp (realizePathCellSig a) (realizePathCellSig b)`.  The exact obstruction is the `vcompIdLeft` row:
`TwoCellStep.vcompIdLeft` maps to `vcomp (id (realize F)) (toCell α) ⟶ toCell α`, whose reduction via the strict
`vcompUnitLeft` axiom requires `id (realize F) ~ id (boundarySource (toCell α))`, i.e. an `id`-congruence lifting
the (conv, not defeq) `realize F ~ boundarySource (toCell α)`.  Discharging the conv-leg needs either an
`idCongr` + whisker-1-cell-congruence extension of `SaturatedConvOver` (a strengthening left for the OMEGA-2
congruence-completion), or a normalising `toCell` — deliberately deferred, not smuggled.  `bridgeDimTwoHolds`
keeps its r1 name and meaning as the (still-open, conv-leg) statement; the PROVEN half ships as
`bridgeDimTwoForwardSize`. -/

/-- **Realise a modality path as a formal 1-cell over the SIGNATURE's computad** — the `computadOfSignature`
analogue of `realizePathCell` (`Omega/CollapseDimOne.lean`).  Empty path ↦ identity 1-cell; `cons` ↦ `vcomp` of
the head modality generator with the realised tail.  Constant return type `CellExpr .. 1` — propext-free. -/
def realizePathCellSig {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    ModalityPath signature.graph sourceMode targetMode →
    CellExpr (computadOfSignature signature) 1
  | _, _, .nil mode => CellExpr.id (CellExpr.ofMode mode)
  | sourceMode, _, @ModalityPath.cons _ _ middleMode _ modality rest =>
      CellExpr.vcomp
        (CellExpr.gen (dim := 0)
          (⟨sourceMode, middleMode, modality⟩ : signatureGenLabel signature 1)
          (CellExpr.ofMode sourceMode) (CellExpr.ofMode middleMode))
        (realizePathCellSig rest)

/-- ★ The **dim-2 bridge translation** — the concrete `DimTwoTranslation`: forget the boundary index of a
`RawTwoCellExpr` into the extrinsic `CellExpr .. 2`, mapping each of the five generators to its `CellExpr`
namesake (the boundary 1-cells realised by `realizePathCellSig`).  Structural recursion, constant `CellExpr .. 2`
return type — propext-free. -/
def toCellDimTwo {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → CellExpr (computadOfSignature signature) 2
  | sourceMode, targetMode, sourcePath, targetPath, .gen twoCell =>
      CellExpr.gen (dim := 1)
        (⟨sourceMode, targetMode, sourcePath, targetPath, twoCell⟩ : signatureGenLabel signature 2)
        (realizePathCellSig sourcePath) (realizePathCellSig targetPath)
  | _, _, _, _, .id path => CellExpr.id (realizePathCellSig path)
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      CellExpr.vcomp (toCellDimTwo cellAlpha) (toCellDimTwo cellBeta)
  | _, _, _, _, .whiskerLeft oneCell cellBeta =>
      CellExpr.whiskerLeft (realizePathCellSig oneCell) (toCellDimTwo cellBeta)
  | _, _, _, _, .whiskerRight oneCell cellAlpha =>
      CellExpr.whiskerRight (toCellDimTwo cellAlpha) (realizePathCellSig oneCell)

/-- ★ **The forward-size leg is a homomorphism.**  `toCellDimTwo` preserves the structural size: every
`RawTwoCellExpr` generator maps to a `CellExpr` generator of equal size, and composites add.  By induction on the
2-cell. -/
theorem toCellDimTwo_size {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    cellSize (toCellDimTwo cell) = cell.size := by
  induction cell with
  | gen _ => rfl
  | id _ => rfl
  | vcomp cellAlpha cellBeta ihAlpha ihBeta =>
      show cellSize (toCellDimTwo cellAlpha) + cellSize (toCellDimTwo cellBeta) + 1
        = cellAlpha.size + cellBeta.size + 1
      rw [ihAlpha, ihBeta]
  | whiskerLeft _ cellBeta ihBeta =>
      show cellSize (toCellDimTwo cellBeta) + 1 = cellBeta.size + 1
      rw [ihBeta]
  | whiskerRight _ cellAlpha ihAlpha =>
      show cellSize (toCellDimTwo cellAlpha) + 1 = cellAlpha.size + 1
      rw [ihAlpha]

/-- ★ **The forward-size half of `bridgeDimTwoHolds`, PROVEN.**  A dim-2 translation exists preserving the
structural size — `toCellDimTwo` witnesses it.  This is the size-preservation conjunct of `bridgeDimTwoHolds`
(the conv-leg conjunct is the named wall above). -/
theorem bridgeDimTwoForwardSize (signature : ModeSignature) :
    ∃ toCell : DimTwoTranslation signature,
      ∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        (cell : RawTwoCellExpr signature sourcePath targetPath),
        cellSize (toCell cell) = cell.size :=
  ⟨@toCellDimTwo signature, fun cell => toCellDimTwo_size cell⟩

end FX1Poly.Polygraph.Omega
