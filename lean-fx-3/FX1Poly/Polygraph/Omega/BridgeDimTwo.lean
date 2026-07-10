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

/-- ★ **STATEMENT (r2 proves): the n=2 bridge to `RawTwoCellExpr`.**  There exists a dim-2 translation that
(1) preserves the structural size and (2) carries the free dim-2 convertibility `TwoCellConv` into the free
strict congruence `freeStrictCongruence emptyPresentation` on the generic carrier.  This is the T1.bridge-n2
claim; it is a forward-declared proposition (defining it introduces no axiom), and r2 constructs the translation
and discharges both legs.  The reverse direction (surjectivity up to convertibility, exhibiting `CellExpr 2`
generators as `RawTwoCellExpr` images) is the companion r2 obligation noted in the file header. -/
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

end FX1Poly.Polygraph.Omega
