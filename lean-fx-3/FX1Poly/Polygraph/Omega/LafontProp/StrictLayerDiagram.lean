import FX1Poly.Polygraph.Omega.LafontProp.ConvertibilitySoundness

/-! # Polygraph/Omega/LafontProp/StrictLayerDiagram — the unbiased strict-layer carrier
(LAFONT-REPAIR stage 1, brick A+B: THE CARRIER THAT DISSOLVES THE PADDING HOLE)

The r3 decision (`CanonicalReduction.lean`) refuted `canonicalReductionStatement` and
`matNatCompletenessStatement` over the binary-tensor syntax: the 28-constructor congruence
carries NO strict-monoidal padding coherence, a Z2 anomaly-parity invariant conserves the
statable strictness instance, and `id0 | delta` is an equal-matrix NON-convertible pair.  The
recorded repair bill offered three routes; this file executes route (ii): REBUILD THE SYNTAX
UNBIASED/STRICT — flat layer lists with definitional concatenation, so the padding coherences
are not new relations but LITERAL `rfl`.

## The literature shape being transcribed

* [DelpeuchVicary2018] A. Delpeuch, J. Vicary, *Normalization for planar string diagrams and a
  quadratic equivalence algorithm*, LMCS 18(1) (2022), arXiv:1804.07832: diagrams as lists of
  slices; identity wires are NOT cells but numeric offsets, so "padding disappears because
  identities are arithmetic, not syntax."  Here a diagram is a list of LAYERS (multi-cell
  slices) and the identity diagram is the EMPTY list — tensoring with `id0` is definitionally
  invisible (`sldPaddingDissolvesOnCopy` is `rfl`; the r3 separator's two sides become EQUAL
  syntax).
* [Lafont2003] Y. Lafont, *Towards an algebraic theory of Boolean circuits*, JPAA 184 (2003),
  Section 3: the five generators tau, delta, epsilon, mu, eta with their Mat(N) matrices;
  "Vertical composition corresponds to the product of matrices, and horizontal composition to
  the direct sum."  The layer semantics below folds exactly that: per-layer block-diagonal
  assembly, per-diagram product.
* [Mimram] S. Mimram, *Presenting a free PROP*: swap as an ordinary generator cell
  (`SldCell.crossing`) rather than permutations-between-layers — the presentation-friendly
  route every mechanized completeness attempt uses.

## The carrier

`SldCell` — six cells with FIXED arities: wire 1->1, mu 2->1, eta 0->1, delta 1->2,
epsilon 1->0, crossing 2->2.  `SldLayer := List SldCell` (horizontal juxtaposition, top block
first, arities are cons-only fold sums).  `SldDiagram := {sourceArity : Nat, layers : List
SldLayer}` with the `Bool` chain predicate `sldIsComposable` (consecutive boundaries meet) and
computed `sldTargetArity`.  Sequential composition IS layer-list concatenation
(`sldAppendLayers`); the category laws are `rfl` / one-lemma rewrites — every `;` coherence of
the old syntax is definitional here.  Parallel tensor zips layers side by side
(`sldZipLayersWithPads`), wire-padding ONLY the shorter list's missing levels — a zero-arity
pad is the empty cell list, so `id0 | D = D` holds definitionally (`sldTensorWithEmptyTopIsSelf`
/ `...BottomIsSelf`), THE design win that kills the r3 anomaly at the syntax level.

## The semantics (Mat(N), reusing the lane's entries kit)

`sldCellEntries` maps cells to the r1 generator matrices; `sldLayerEntries` folds
`directSumEntries` (block-diagonal, top block first); `sldLayersDenote` folds `composeEntries`
(second stage on the left).  The BLOCK ALGEBRA section proves, pointwise on entries, the
lemmas the old syntax got from its congruence induction: product congruence/associativity/
identity collapses, direct-sum congruence/identity-fusion/ASSOCIATIVITY (the lemma the binary
syntax could not even state cast-free)/MULTIPLICATIVITY (the pointed-tensor engine), the
wire-layer-is-identity computation, and the layer-append-as-blocks decomposition.  On top:
THE TWO FUNCTORIALITY THEOREMS — denote of append is the matrix product
(`sldDenoteOfAppendAsProductEntry`, unconditional), denote of the zip tensor is the direct sum
(`sldDenoteOfZipAsDirectSumEntry`, under boundary composability).

## The defensive fires (stage D of the commission, the file-1 half)

* FIRE (1a): `sldPaddingDissolvesOnCopy` / `sldPaddingDissolvesOnCopyBelow` — `id0 | delta`
  and `delta | id0` are the SAME `SldDiagram` as bare `delta`, by kernel `rfl`.  The r3
  anomaly-parity separator cannot even be STATED here: there is no tensor node to weigh.
* FIRE (1b): the open-diagram forms `sldTensorWithEmptyTopIsSelf` / `...BottomIsSelf` (every
  diagram, one `Nat.zero_add` / nil-append lemma away from `rfl`).
* FIRE (3): the Z2 negative control SURVIVES the rebuild — `mu . delta` vs `eta . epsilon`
  still have DIFFERENT matrices (`sldZSpecificPairStillSeparates`, kernel `rfl`): the carrier
  dissolved the padding anomaly WITHOUT collapsing the semantics.

The congruence, the 18 relation rows as layer windows, soundness, and the embedding of the old
`WireDiagram` syntax live in the stage-2 file `StrictLayerEmbedding.lean`.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## The six strict-layer cells and their fixed arities -/

/-- One cell of a layer: an identity wire, one of the five Lafont generators, or the adjacent
transposition.  Wire IS a cell here (multi-cell layers); the empty-TENSOR padding is what the
carrier makes definitional, not the single wire. -/
inductive SldCell : Type where
  | wire : SldCell
  | generatorMu : SldCell
  | generatorEta : SldCell
  | generatorDelta : SldCell
  | generatorEpsilon : SldCell
  | crossing : SldCell

/-- Source arity (input strand count) of a cell. -/
def sldCellSourceArity : SldCell -> Nat
  | SldCell.wire => 1
  | SldCell.generatorMu => 2
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 1
  | SldCell.generatorEpsilon => 1
  | SldCell.crossing => 2

/-- Target arity (output strand count) of a cell. -/
def sldCellTargetArity : SldCell -> Nat
  | SldCell.wire => 1
  | SldCell.generatorMu => 1
  | SldCell.generatorEta => 1
  | SldCell.generatorDelta => 2
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 2

/-! ## Layers: horizontal cell lists (top block first) -/

/-- A layer is a horizontal juxtaposition of cells, top block first. -/
abbrev SldLayer : Type := List SldCell

/-- Fold a per-cell arity over a layer (cons-only sum). -/
def sldLayerArityBy (cellArity : SldCell -> Nat) : SldLayer -> Nat
  | [] => 0
  | headCell :: tailCells => cellArity headCell + sldLayerArityBy cellArity tailCells

/-- Source arity of a layer. -/
def sldLayerSourceArity : SldLayer -> Nat := sldLayerArityBy sldCellSourceArity

/-- Target arity of a layer. -/
def sldLayerTargetArity : SldLayer -> Nat := sldLayerArityBy sldCellTargetArity

/-- Cons-only append of two layers (no `List.append`, per the lane's leak discipline). -/
def sldAppendCells : SldLayer -> SldLayer -> SldLayer
  | [], secondCells => secondCells
  | headCell :: tailCells, secondCells => headCell :: sldAppendCells tailCells secondCells

/-- Appending the empty layer on the right is the identity. -/
theorem sldAppendCellsNilRightIsSelf : (cells : SldLayer) -> sldAppendCells cells [] = cells
  | [] => rfl
  | headCell :: tailCells =>
      congrArg (fun restCells => headCell :: restCells) (sldAppendCellsNilRightIsSelf tailCells)

/-- Cell-append is associative. -/
theorem sldAppendCellsAssoc : (firstCells secondCells thirdCells : SldLayer) ->
    sldAppendCells (sldAppendCells firstCells secondCells) thirdCells
      = sldAppendCells firstCells (sldAppendCells secondCells thirdCells)
  | [], _, _ => rfl
  | headCell :: tailCells, secondCells, thirdCells =>
      congrArg (fun restCells => headCell :: restCells)
        (sldAppendCellsAssoc tailCells secondCells thirdCells)

/-- Any arity fold distributes over cell-append as a sum. -/
theorem sldAppendCellsArityBy (cellArity : SldCell -> Nat) :
    (firstCells secondCells : SldLayer) ->
    sldLayerArityBy cellArity (sldAppendCells firstCells secondCells)
      = sldLayerArityBy cellArity firstCells + sldLayerArityBy cellArity secondCells
  | [], secondCells => (Nat.zero_add (sldLayerArityBy cellArity secondCells)).symm
  | headCell :: tailCells, secondCells => by
      show cellArity headCell + sldLayerArityBy cellArity (sldAppendCells tailCells secondCells)
        = (cellArity headCell + sldLayerArityBy cellArity tailCells)
          + sldLayerArityBy cellArity secondCells
      rw [sldAppendCellsArityBy cellArity tailCells secondCells]
      exact (Nat.add_assoc (cellArity headCell) (sldLayerArityBy cellArity tailCells)
        (sldLayerArityBy cellArity secondCells)).symm

/-- Source arity of an appended layer is the sum of the parts'. -/
theorem sldAppendCellsSourceArity (firstCells secondCells : SldLayer) :
    sldLayerSourceArity (sldAppendCells firstCells secondCells)
      = sldLayerSourceArity firstCells + sldLayerSourceArity secondCells :=
  sldAppendCellsArityBy sldCellSourceArity firstCells secondCells

/-- Target arity of an appended layer is the sum of the parts'. -/
theorem sldAppendCellsTargetArity (firstCells secondCells : SldLayer) :
    sldLayerTargetArity (sldAppendCells firstCells secondCells)
      = sldLayerTargetArity firstCells + sldLayerTargetArity secondCells :=
  sldAppendCellsArityBy sldCellTargetArity firstCells secondCells

/-! ## Wire layers: the identity as a layer of wire cells -/

/-- The layer of `strandCount` identity wires. -/
def sldWireLayerOfArity : Nat -> SldLayer
  | 0 => []
  | strandPred + 1 => SldCell.wire :: sldWireLayerOfArity strandPred

/-- Any arity fold on a wire layer counts the strands (wire arities are 1 on both sides). -/
theorem sldWireLayerArityBy (cellArity : SldCell -> Nat)
    (isWireAritySingle : cellArity SldCell.wire = 1) :
    (strandCount : Nat) -> sldLayerArityBy cellArity (sldWireLayerOfArity strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show cellArity SldCell.wire + sldLayerArityBy cellArity (sldWireLayerOfArity strandPred)
        = strandPred + 1
      rw [isWireAritySingle, sldWireLayerArityBy cellArity isWireAritySingle strandPred]
      exact Nat.add_comm 1 strandPred

/-- Source arity of a wire layer. -/
theorem sldWireLayerSourceArity (strandCount : Nat) :
    sldLayerSourceArity (sldWireLayerOfArity strandCount) = strandCount :=
  sldWireLayerArityBy sldCellSourceArity rfl strandCount

/-- Target arity of a wire layer. -/
theorem sldWireLayerTargetArity (strandCount : Nat) :
    sldLayerTargetArity (sldWireLayerOfArity strandCount) = strandCount :=
  sldWireLayerArityBy sldCellTargetArity rfl strandCount

/-- Wire layers split additively: `wires(a) ++ wires(b) = wires(a + b)`. -/
theorem sldWireLayerSplitsAtCount : (firstCount secondCount : Nat) ->
    sldAppendCells (sldWireLayerOfArity firstCount) (sldWireLayerOfArity secondCount)
      = sldWireLayerOfArity (firstCount + secondCount)
  | 0, secondCount => by
      rw [Nat.zero_add]
      rfl
  | firstPred + 1, secondCount => by
      rw [Nat.succ_add firstPred secondCount]
      show SldCell.wire
          :: sldAppendCells (sldWireLayerOfArity firstPred) (sldWireLayerOfArity secondCount)
        = SldCell.wire :: sldWireLayerOfArity (firstPred + secondCount)
      rw [sldWireLayerSplitsAtCount firstPred secondCount]

/-! ## Diagrams: a source arity plus a layer list -/

/-- A strict-layer diagram: the global source arity (needed by the empty list — the identity
diagram) plus the vertical list of layers, first stage first. -/
structure SldDiagram where
  sourceArity : Nat
  layers : List SldLayer

/-- Do consecutive layer boundaries meet, starting from the given source boundary? -/
def sldLayersAreComposableFrom : Nat -> List SldLayer -> Bool
  | _boundaryArity, [] => true
  | boundaryArity, headLayer :: tailLayers =>
      Nat.beq (sldLayerSourceArity headLayer) boundaryArity
        && sldLayersAreComposableFrom (sldLayerTargetArity headLayer) tailLayers

/-- Target boundary reached by walking the layer list from the given source boundary. -/
def sldLayersTargetArityFrom : Nat -> List SldLayer -> Nat
  | boundaryArity, [] => boundaryArity
  | _boundaryArity, headLayer :: tailLayers =>
      sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers

/-- Well-formedness of a diagram: the layer chain composes from the declared source. -/
def sldIsComposable (diagram : SldDiagram) : Bool :=
  sldLayersAreComposableFrom diagram.sourceArity diagram.layers

/-- Target arity of a diagram. -/
def sldTargetArity (diagram : SldDiagram) : Nat :=
  sldLayersTargetArityFrom diagram.sourceArity diagram.layers

/-! ## Sequential composition = layer-list concatenation -/

/-- Cons-only append of two layer lists. -/
def sldAppendLayers : List SldLayer -> List SldLayer -> List SldLayer
  | [], secondLayers => secondLayers
  | headLayer :: tailLayers, secondLayers => headLayer :: sldAppendLayers tailLayers secondLayers

/-- Appending the empty layer list on the right is the identity. -/
theorem sldAppendLayersNilRightIsSelf : (layers : List SldLayer) -> sldAppendLayers layers [] = layers
  | [] => rfl
  | headLayer :: tailLayers =>
      congrArg (fun restLayers => headLayer :: restLayers)
        (sldAppendLayersNilRightIsSelf tailLayers)

/-- Layer-list append is associative. -/
theorem sldAppendLayersAssoc : (firstLayers secondLayers thirdLayers : List SldLayer) ->
    sldAppendLayers (sldAppendLayers firstLayers secondLayers) thirdLayers
      = sldAppendLayers firstLayers (sldAppendLayers secondLayers thirdLayers)
  | [], _, _ => rfl
  | headLayer :: tailLayers, secondLayers, thirdLayers =>
      congrArg (fun restLayers => headLayer :: restLayers)
        (sldAppendLayersAssoc tailLayers secondLayers thirdLayers)

/-- Walking an appended list is walking the parts in sequence. -/
theorem sldAppendLayersTargetArityFrom :
    (firstLayers : List SldLayer) -> (boundaryArity : Nat) -> (secondLayers : List SldLayer) ->
    sldLayersTargetArityFrom boundaryArity (sldAppendLayers firstLayers secondLayers)
      = sldLayersTargetArityFrom (sldLayersTargetArityFrom boundaryArity firstLayers) secondLayers
  | [], _, _ => rfl
  | headLayer :: tailLayers, _boundaryArity, secondLayers =>
      sldAppendLayersTargetArityFrom tailLayers (sldLayerTargetArity headLayer) secondLayers

/-- Composability joins across an append when the middle boundary meets. -/
theorem sldComposableFromAppendOfParts :
    (firstLayers : List SldLayer) -> (boundaryArity : Nat) -> (secondLayers : List SldLayer) ->
    sldLayersAreComposableFrom boundaryArity firstLayers = true ->
    sldLayersAreComposableFrom (sldLayersTargetArityFrom boundaryArity firstLayers) secondLayers
      = true ->
    sldLayersAreComposableFrom boundaryArity (sldAppendLayers firstLayers secondLayers) = true
  | [], _, _, _, isSecondComposable => isSecondComposable
  | headLayer :: tailLayers, boundaryArity, secondLayers, isFirstComposable,
      isSecondComposable => by
      have doesHeadFit : Nat.beq (sldLayerSourceArity headLayer) boundaryArity = true :=
        leftIsTrueOfAndTrue isFirstComposable
      have doesTailCompose := rightIsTrueOfAndTrue isFirstComposable
      show (Nat.beq (sldLayerSourceArity headLayer) boundaryArity
        && sldLayersAreComposableFrom (sldLayerTargetArity headLayer)
            (sldAppendLayers tailLayers secondLayers)) = true
      rw [doesHeadFit,
        sldComposableFromAppendOfParts tailLayers (sldLayerTargetArity headLayer) secondLayers
          doesTailCompose isSecondComposable]
      rfl

/-- Composability of an append gives composability of the first part. -/
theorem sldComposableFromAppendGivesFirst :
    (firstLayers : List SldLayer) -> (boundaryArity : Nat) -> (secondLayers : List SldLayer) ->
    sldLayersAreComposableFrom boundaryArity (sldAppendLayers firstLayers secondLayers) = true ->
    sldLayersAreComposableFrom boundaryArity firstLayers = true
  | [], _, _, _ => rfl
  | headLayer :: tailLayers, boundaryArity, secondLayers, isWholeComposable => by
      have doesHeadFit := leftIsTrueOfAndTrue isWholeComposable
      have doesTailCompose := sldComposableFromAppendGivesFirst tailLayers
        (sldLayerTargetArity headLayer) secondLayers (rightIsTrueOfAndTrue isWholeComposable)
      show (Nat.beq (sldLayerSourceArity headLayer) boundaryArity
        && sldLayersAreComposableFrom (sldLayerTargetArity headLayer) tailLayers) = true
      rw [doesHeadFit, doesTailCompose]
      rfl

/-- Composability of an append gives composability of the second part at the middle boundary. -/
theorem sldComposableFromAppendGivesSecond :
    (firstLayers : List SldLayer) -> (boundaryArity : Nat) -> (secondLayers : List SldLayer) ->
    sldLayersAreComposableFrom boundaryArity (sldAppendLayers firstLayers secondLayers) = true ->
    sldLayersAreComposableFrom (sldLayersTargetArityFrom boundaryArity firstLayers) secondLayers
      = true
  | [], _, _, isWholeComposable => isWholeComposable
  | headLayer :: tailLayers, _boundaryArity, secondLayers, isWholeComposable =>
      sldComposableFromAppendGivesSecond tailLayers (sldLayerTargetArity headLayer) secondLayers
        (rightIsTrueOfAndTrue isWholeComposable)

/-- The identity diagram: the EMPTY layer list.  There is no id-cell stack — identities are
absent syntax, exactly the [DelpeuchVicary2018] design that dissolves padding. -/
def sldIdentityDiagram (strandCount : Nat) : SldDiagram :=
  { sourceArity := strandCount, layers := [] }

/-- Sequential composition: concatenate the layer lists (first stage first). -/
def sldComposeSequential (firstDiagram secondDiagram : SldDiagram) : SldDiagram :=
  { sourceArity := firstDiagram.sourceArity
  , layers := sldAppendLayers firstDiagram.layers secondDiagram.layers }

/-- LEFT IDENTITY LAW, definitionally: `id ; D = D` by kernel `rfl` — the coherence the old
syntax carried as a congruence constructor is nothing here. -/
theorem sldComposeWithIdentitySourceIsSelf (diagram : SldDiagram) :
    sldComposeSequential (sldIdentityDiagram diagram.sourceArity) diagram = diagram := rfl

/-- RIGHT IDENTITY LAW: `D ; id = D` (one nil-append rewrite). -/
theorem sldComposeWithIdentityTargetIsSelf (diagram : SldDiagram) :
    sldComposeSequential diagram (sldIdentityDiagram (sldTargetArity diagram)) = diagram := by
  show SldDiagram.mk diagram.sourceArity (sldAppendLayers diagram.layers []) = diagram
  rw [sldAppendLayersNilRightIsSelf diagram.layers]

/-- ASSOCIATIVITY of sequential composition (one append-assoc rewrite; the old syntax carried
this as the `composeReassociate` constructor). -/
theorem sldComposeSequentialAssoc (firstDiagram secondDiagram thirdDiagram : SldDiagram) :
    sldComposeSequential (sldComposeSequential firstDiagram secondDiagram) thirdDiagram
      = sldComposeSequential firstDiagram (sldComposeSequential secondDiagram thirdDiagram) := by
  show SldDiagram.mk firstDiagram.sourceArity
      (sldAppendLayers (sldAppendLayers firstDiagram.layers secondDiagram.layers)
        thirdDiagram.layers)
    = SldDiagram.mk firstDiagram.sourceArity
        (sldAppendLayers firstDiagram.layers
          (sldAppendLayers secondDiagram.layers thirdDiagram.layers))
  rw [sldAppendLayersAssoc firstDiagram.layers secondDiagram.layers thirdDiagram.layers]

/-- Target arity of a composite (boundaries meeting). -/
theorem sldComposeSequentialTargetArity (firstDiagram secondDiagram : SldDiagram)
    (doBoundariesMeet : secondDiagram.sourceArity = sldTargetArity firstDiagram) :
    sldTargetArity (sldComposeSequential firstDiagram secondDiagram)
      = sldTargetArity secondDiagram := by
  show sldLayersTargetArityFrom firstDiagram.sourceArity
      (sldAppendLayers firstDiagram.layers secondDiagram.layers)
    = sldLayersTargetArityFrom secondDiagram.sourceArity secondDiagram.layers
  rw [sldAppendLayersTargetArityFrom firstDiagram.layers firstDiagram.sourceArity
    secondDiagram.layers, doBoundariesMeet]
  rfl

/-- Composability of a composite (boundaries meeting). -/
theorem sldComposeSequentialIsComposable (firstDiagram secondDiagram : SldDiagram)
    (isFirstComposable : sldIsComposable firstDiagram = true)
    (isSecondComposable : sldIsComposable secondDiagram = true)
    (doBoundariesMeet : secondDiagram.sourceArity = sldTargetArity firstDiagram) :
    sldIsComposable (sldComposeSequential firstDiagram secondDiagram) = true := by
  show sldLayersAreComposableFrom firstDiagram.sourceArity
    (sldAppendLayers firstDiagram.layers secondDiagram.layers) = true
  refine sldComposableFromAppendOfParts firstDiagram.layers firstDiagram.sourceArity
    secondDiagram.layers isFirstComposable ?_
  have isSecondFromSource : sldLayersAreComposableFrom secondDiagram.sourceArity
      secondDiagram.layers = true := isSecondComposable
  rw [doBoundariesMeet] at isSecondFromSource
  exact isSecondFromSource

/-! ## Parallel tensor = zip with wire pads on the shorter list only -/

/-- Pad every layer of a bottom-block remainder with wires ABOVE (the finished top block's
strands continue as wires). -/
def sldPadLayersAbove (padCount : Nat) : List SldLayer -> List SldLayer
  | [] => []
  | headLayer :: tailLayers =>
      sldAppendCells (sldWireLayerOfArity padCount) headLayer
        :: sldPadLayersAbove padCount tailLayers

/-- Pad every layer of a top-block remainder with wires BELOW. -/
def sldPadLayersBelow (padCount : Nat) : List SldLayer -> List SldLayer
  | [] => []
  | headLayer :: tailLayers =>
      sldAppendCells headLayer (sldWireLayerOfArity padCount)
        :: sldPadLayersBelow padCount tailLayers

/-- Zip two layer lists side by side (top block first inside each layer); when one list runs
out, its final boundary continues as a wire pad on the survivor's layers.  A ZERO-arity pad is
the EMPTY cell list — this is where `id0`-tensoring becomes definitionally invisible. -/
def sldZipLayersWithPads (topFinalArity bottomFinalArity : Nat) :
    List SldLayer -> List SldLayer -> List SldLayer
  | [], bottomLayers => sldPadLayersAbove topFinalArity bottomLayers
  | topHead :: topTail, [] => sldPadLayersBelow bottomFinalArity (topHead :: topTail)
  | topHead :: topTail, bottomHead :: bottomTail =>
      sldAppendCells topHead bottomHead
        :: sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail

/-- Parallel tensor: sum the source arities, zip the layers with final-boundary wire pads. -/
def sldTensorParallel (topDiagram bottomDiagram : SldDiagram) : SldDiagram :=
  { sourceArity := topDiagram.sourceArity + bottomDiagram.sourceArity
  , layers := sldZipLayersWithPads (sldTargetArity topDiagram) (sldTargetArity bottomDiagram)
      topDiagram.layers bottomDiagram.layers }

/-- A zero-arity above-pad is invisible. -/
theorem sldPadLayersAboveWithZeroIsSelf : (bottomLayers : List SldLayer) ->
    sldPadLayersAbove 0 bottomLayers = bottomLayers
  | [] => rfl
  | bottomHead :: bottomTail =>
      congrArg (fun restLayers => bottomHead :: restLayers)
        (sldPadLayersAboveWithZeroIsSelf bottomTail)

/-- A zero-arity below-pad is invisible (nil-append per layer). -/
theorem sldPadLayersBelowWithZeroIsSelf : (topLayers : List SldLayer) ->
    sldPadLayersBelow 0 topLayers = topLayers
  | [] => rfl
  | topHead :: topTail => by
      show sldAppendCells topHead [] :: sldPadLayersBelow 0 topTail = topHead :: topTail
      rw [sldAppendCellsNilRightIsSelf topHead, sldPadLayersBelowWithZeroIsSelf topTail]

/-! ### THE PADDING DISSOLUTION (defensive fire 1, the whole point of the rebuild)

The r3 refutation hinged on `id0 | delta` being SYNTACTICALLY distinct from `delta` with no
congruence path between them.  Here they are the SAME term. -/

/-- THE KEY DESIGN WIN, top form: tensoring `id0` above ANY diagram is the diagram (the
`0 + sourceArity` index and the zero pad both vanish). -/
theorem sldTensorWithEmptyTopIsSelf (diagram : SldDiagram) :
    sldTensorParallel (sldIdentityDiagram 0) diagram = diagram := by
  show SldDiagram.mk (0 + diagram.sourceArity) (sldPadLayersAbove 0 diagram.layers) = diagram
  rw [Nat.zero_add, sldPadLayersAboveWithZeroIsSelf diagram.layers]

/-- THE KEY DESIGN WIN, bottom form: tensoring `id0` below ANY diagram is the diagram. -/
theorem sldTensorWithEmptyBottomIsSelf (diagram : SldDiagram) :
    sldTensorParallel diagram (sldIdentityDiagram 0) = diagram := by
  cases diagram with
  | mk sourceArity layers =>
      cases layers with
      | nil => rfl
      | cons headLayer tailLayers =>
          show SldDiagram.mk (sourceArity + 0)
              (sldPadLayersBelow 0 (headLayer :: tailLayers))
            = SldDiagram.mk sourceArity (headLayer :: tailLayers)
          rw [sldPadLayersBelowWithZeroIsSelf (headLayer :: tailLayers)]
          rfl

/-- The bare copy generator as a strict-layer diagram. -/
def sldCopyDiagram : SldDiagram :=
  { sourceArity := 1, layers := [[SldCell.generatorDelta]] }

/-- DEFENSIVE FIRE (1a): the r3 separator DISSOLVES — `id0 | delta` IS `delta`, kernel `rfl`.
The anomaly-parity invariant that refuted the old completeness has nothing left to weigh. -/
theorem sldPaddingDissolvesOnCopy :
    sldTensorParallel (sldIdentityDiagram 0) sldCopyDiagram = sldCopyDiagram := rfl

/-- DEFENSIVE FIRE (1a'), mirror: `delta | id0` IS `delta`, kernel `rfl`. -/
theorem sldPaddingDissolvesOnCopyBelow :
    sldTensorParallel sldCopyDiagram (sldIdentityDiagram 0) = sldCopyDiagram := rfl

/-! ### Boundary bookkeeping for the pads and the zip -/

/-- An above-padded block chain composes from the pad-shifted boundary. -/
theorem sldPadLayersAboveAreComposableFrom (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    sldLayersAreComposableFrom (padCount + blockBoundary)
      (sldPadLayersAbove padCount blockLayers) = true
  | [], _, _ => rfl
  | blockHead :: blockTail, blockBoundary, isChainComposable => by
      have doesHeadMatch : sldLayerSourceArity blockHead = blockBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      show (Nat.beq
          (sldLayerSourceArity (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
          (padCount + blockBoundary)
        && sldLayersAreComposableFrom
            (sldLayerTargetArity (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
            (sldPadLayersAbove padCount blockTail)) = true
      rw [sldAppendCellsSourceArity, sldWireLayerSourceArity, doesHeadMatch, beqSelfIsTrue,
        sldAppendCellsTargetArity, sldWireLayerTargetArity,
        sldPadLayersAboveAreComposableFrom padCount blockTail (sldLayerTargetArity blockHead)
          doesTailCompose]
      rfl

/-- Walking an above-padded block shifts the reached boundary by the pad. -/
theorem sldPadLayersAboveTargetArityFrom (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersTargetArityFrom (padCount + blockBoundary) (sldPadLayersAbove padCount blockLayers)
      = padCount + sldLayersTargetArityFrom blockBoundary blockLayers
  | [], _ => rfl
  | blockHead :: blockTail, _blockBoundary => by
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
          (sldPadLayersAbove padCount blockTail)
        = padCount + sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact sldPadLayersAboveTargetArityFrom padCount blockTail (sldLayerTargetArity blockHead)

/-- A below-padded block chain composes from the pad-shifted boundary. -/
theorem sldPadLayersBelowAreComposableFrom (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    sldLayersAreComposableFrom (blockBoundary + padCount)
      (sldPadLayersBelow padCount blockLayers) = true
  | [], _, _ => rfl
  | blockHead :: blockTail, blockBoundary, isChainComposable => by
      have doesHeadMatch : sldLayerSourceArity blockHead = blockBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      show (Nat.beq
          (sldLayerSourceArity (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
          (blockBoundary + padCount)
        && sldLayersAreComposableFrom
            (sldLayerTargetArity (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
            (sldPadLayersBelow padCount blockTail)) = true
      rw [sldAppendCellsSourceArity, sldWireLayerSourceArity, doesHeadMatch, beqSelfIsTrue,
        sldAppendCellsTargetArity, sldWireLayerTargetArity,
        sldPadLayersBelowAreComposableFrom padCount blockTail (sldLayerTargetArity blockHead)
          doesTailCompose]
      rfl

/-- Walking a below-padded block shifts the reached boundary by the pad. -/
theorem sldPadLayersBelowTargetArityFrom (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersTargetArityFrom (blockBoundary + padCount) (sldPadLayersBelow padCount blockLayers)
      = sldLayersTargetArityFrom blockBoundary blockLayers + padCount
  | [], _ => rfl
  | blockHead :: blockTail, _blockBoundary => by
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
          (sldPadLayersBelow padCount blockTail)
        = sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail + padCount
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact sldPadLayersBelowTargetArityFrom padCount blockTail (sldLayerTargetArity blockHead)

/-- The zip of two composable chains composes from the summed boundary. -/
theorem sldZipLayersAreComposableFrom (topFinalArity bottomFinalArity : Nat) :
    (topLayers bottomLayers : List SldLayer) -> (topBoundary bottomBoundary : Nat) ->
    sldLayersAreComposableFrom topBoundary topLayers = true ->
    sldLayersAreComposableFrom bottomBoundary bottomLayers = true ->
    sldLayersTargetArityFrom topBoundary topLayers = topFinalArity ->
    sldLayersTargetArityFrom bottomBoundary bottomLayers = bottomFinalArity ->
    sldLayersAreComposableFrom (topBoundary + bottomBoundary)
      (sldZipLayersWithPads topFinalArity bottomFinalArity topLayers bottomLayers) = true
  | [], bottomLayers, topBoundary, bottomBoundary, _, isBottomComposable, isTopReached, _ => by
      have isTopPinned : topBoundary = topFinalArity := isTopReached
      show sldLayersAreComposableFrom (topBoundary + bottomBoundary)
        (sldPadLayersAbove topFinalArity bottomLayers) = true
      rw [isTopPinned]
      exact sldPadLayersAboveAreComposableFrom topFinalArity bottomLayers bottomBoundary
        isBottomComposable
  | topHead :: topTail, [], topBoundary, bottomBoundary, isTopComposable, _, _,
      isBottomReached => by
      have isBottomPinned : bottomBoundary = bottomFinalArity := isBottomReached
      have doesHeadMatch : sldLayerSourceArity topHead = topBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isTopComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isTopComposable
      show (Nat.beq
          (sldLayerSourceArity (sldAppendCells topHead (sldWireLayerOfArity bottomFinalArity)))
          (topBoundary + bottomBoundary)
        && sldLayersAreComposableFrom
            (sldLayerTargetArity (sldAppendCells topHead (sldWireLayerOfArity bottomFinalArity)))
            (sldPadLayersBelow bottomFinalArity topTail)) = true
      rw [sldAppendCellsSourceArity, sldWireLayerSourceArity, doesHeadMatch, isBottomPinned,
        beqSelfIsTrue, sldAppendCellsTargetArity, sldWireLayerTargetArity,
        sldPadLayersBelowAreComposableFrom bottomFinalArity topTail
          (sldLayerTargetArity topHead) doesTailCompose]
      rfl
  | topHead :: topTail, bottomHead :: bottomTail, topBoundary, bottomBoundary,
      isTopComposable, isBottomComposable, willTopReach, willBottomReach => by
      have doesTopHeadMatch : sldLayerSourceArity topHead = topBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isTopComposable)
      have doesBottomHeadMatch : sldLayerSourceArity bottomHead = bottomBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isBottomComposable)
      show (Nat.beq (sldLayerSourceArity (sldAppendCells topHead bottomHead))
          (topBoundary + bottomBoundary)
        && sldLayersAreComposableFrom (sldLayerTargetArity (sldAppendCells topHead bottomHead))
            (sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail)) = true
      rw [sldAppendCellsSourceArity, doesTopHeadMatch, doesBottomHeadMatch, beqSelfIsTrue,
        sldAppendCellsTargetArity,
        sldZipLayersAreComposableFrom topFinalArity bottomFinalArity topTail bottomTail
          (sldLayerTargetArity topHead) (sldLayerTargetArity bottomHead)
          (rightIsTrueOfAndTrue isTopComposable) (rightIsTrueOfAndTrue isBottomComposable)
          willTopReach willBottomReach]
      rfl

/-- The zip of two chains reaches the summed final boundary. -/
theorem sldZipLayersTargetArityFrom (topFinalArity bottomFinalArity : Nat) :
    (topLayers bottomLayers : List SldLayer) -> (topBoundary bottomBoundary : Nat) ->
    sldLayersTargetArityFrom topBoundary topLayers = topFinalArity ->
    sldLayersTargetArityFrom bottomBoundary bottomLayers = bottomFinalArity ->
    sldLayersTargetArityFrom (topBoundary + bottomBoundary)
      (sldZipLayersWithPads topFinalArity bottomFinalArity topLayers bottomLayers)
      = topFinalArity + bottomFinalArity
  | [], bottomLayers, topBoundary, bottomBoundary, isTopReached, willBottomReach => by
      have isTopPinned : topBoundary = topFinalArity := isTopReached
      show sldLayersTargetArityFrom (topBoundary + bottomBoundary)
        (sldPadLayersAbove topFinalArity bottomLayers) = topFinalArity + bottomFinalArity
      rw [isTopPinned, sldPadLayersAboveTargetArityFrom topFinalArity bottomLayers bottomBoundary,
        willBottomReach]
  | topHead :: topTail, [], topBoundary, bottomBoundary, willTopReach, isBottomReached => by
      have isBottomPinned : bottomBoundary = bottomFinalArity := isBottomReached
      have willTopTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity topHead) topTail = topFinalArity :=
        willTopReach
      show sldLayersTargetArityFrom (topBoundary + bottomBoundary)
          (sldAppendCells topHead (sldWireLayerOfArity bottomFinalArity)
            :: sldPadLayersBelow bottomFinalArity topTail)
        = topFinalArity + bottomFinalArity
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldAppendCells topHead (sldWireLayerOfArity bottomFinalArity)))
          (sldPadLayersBelow bottomFinalArity topTail)
        = topFinalArity + bottomFinalArity
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity,
        sldPadLayersBelowTargetArityFrom bottomFinalArity topTail (sldLayerTargetArity topHead),
        willTopTailReach]
  | topHead :: topTail, bottomHead :: bottomTail, _topBoundary, _bottomBoundary,
      willTopReach, willBottomReach => by
      have willTopTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity topHead) topTail = topFinalArity :=
        willTopReach
      have willBottomTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity bottomHead) bottomTail
            = bottomFinalArity :=
        willBottomReach
      show sldLayersTargetArityFrom (sldLayerTargetArity (sldAppendCells topHead bottomHead))
          (sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail)
        = topFinalArity + bottomFinalArity
      rw [sldAppendCellsTargetArity]
      exact sldZipLayersTargetArityFrom topFinalArity bottomFinalArity topTail bottomTail
        (sldLayerTargetArity topHead) (sldLayerTargetArity bottomHead)
        willTopTailReach willBottomTailReach

/-- Composability of a tensor. -/
theorem sldTensorParallelIsComposable (topDiagram bottomDiagram : SldDiagram)
    (isTopComposable : sldIsComposable topDiagram = true)
    (isBottomComposable : sldIsComposable bottomDiagram = true) :
    sldIsComposable (sldTensorParallel topDiagram bottomDiagram) = true :=
  sldZipLayersAreComposableFrom (sldTargetArity topDiagram) (sldTargetArity bottomDiagram)
    topDiagram.layers bottomDiagram.layers topDiagram.sourceArity bottomDiagram.sourceArity
    isTopComposable isBottomComposable rfl rfl

/-- Target arity of a tensor is the sum of the target arities. -/
theorem sldTensorParallelTargetArity (topDiagram bottomDiagram : SldDiagram) :
    sldTargetArity (sldTensorParallel topDiagram bottomDiagram)
      = sldTargetArity topDiagram + sldTargetArity bottomDiagram :=
  sldZipLayersTargetArityFrom (sldTargetArity topDiagram) (sldTargetArity bottomDiagram)
    topDiagram.layers bottomDiagram.layers topDiagram.sourceArity bottomDiagram.sourceArity
    rfl rfl

/-! ## Window pads (both sides at once) — the row-embedding combinator of stage C -/

/-- Pad one layer with wires above and below. -/
def sldPadLayer (padAboveCount padBelowCount : Nat) (windowLayer : SldLayer) : SldLayer :=
  sldAppendCells (sldWireLayerOfArity padAboveCount)
    (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount))

/-- Pad every layer of a window with wires above and below — the ONE window-replacement
combinator; every stage-C relation row fires through it. -/
def sldPadWindow (padAboveCount padBelowCount : Nat) : List SldLayer -> List SldLayer
  | [] => []
  | headLayer :: tailLayers =>
      sldPadLayer padAboveCount padBelowCount headLayer
        :: sldPadWindow padAboveCount padBelowCount tailLayers

/-- Source arity of a padded layer. -/
theorem sldPadLayerSourceArity (padAboveCount padBelowCount : Nat) (windowLayer : SldLayer) :
    sldLayerSourceArity (sldPadLayer padAboveCount padBelowCount windowLayer)
      = padAboveCount + (sldLayerSourceArity windowLayer + padBelowCount) := by
  show sldLayerSourceArity (sldAppendCells (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
    = padAboveCount + (sldLayerSourceArity windowLayer + padBelowCount)
  rw [sldAppendCellsSourceArity, sldWireLayerSourceArity, sldAppendCellsSourceArity,
    sldWireLayerSourceArity]

/-- Target arity of a padded layer. -/
theorem sldPadLayerTargetArity (padAboveCount padBelowCount : Nat) (windowLayer : SldLayer) :
    sldLayerTargetArity (sldPadLayer padAboveCount padBelowCount windowLayer)
      = padAboveCount + (sldLayerTargetArity windowLayer + padBelowCount) := by
  show sldLayerTargetArity (sldAppendCells (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
    = padAboveCount + (sldLayerTargetArity windowLayer + padBelowCount)
  rw [sldAppendCellsTargetArity, sldWireLayerTargetArity, sldAppendCellsTargetArity,
    sldWireLayerTargetArity]

/-- The zero pad is invisible on a layer. -/
theorem sldPadLayerZeroIsSelf (windowLayer : SldLayer) : sldPadLayer 0 0 windowLayer = windowLayer := by
  show sldAppendCells windowLayer (sldWireLayerOfArity 0) = windowLayer
  exact sldAppendCellsNilRightIsSelf windowLayer

/-- The zero pad is invisible on a window. -/
theorem sldPadWindowZeroIsSelf : (windowLayers : List SldLayer) ->
    sldPadWindow 0 0 windowLayers = windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldPadLayer 0 0 headLayer :: sldPadWindow 0 0 tailLayers = headLayer :: tailLayers
      rw [sldPadLayerZeroIsSelf headLayer, sldPadWindowZeroIsSelf tailLayers]

/-- Walking a padded window shifts the boundary through unchanged pads. -/
theorem sldPadWindowTargetArityFrom (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) -> (windowBoundary : Nat) ->
    sldLayersTargetArityFrom (padAboveCount + (windowBoundary + padBelowCount))
      (sldPadWindow padAboveCount padBelowCount windowLayers)
      = padAboveCount + (sldLayersTargetArityFrom windowBoundary windowLayers + padBelowCount)
  | [], _ => rfl
  | headLayer :: tailLayers, _windowBoundary => by
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldPadLayer padAboveCount padBelowCount headLayer))
          (sldPadWindow padAboveCount padBelowCount tailLayers)
        = padAboveCount
          + (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers + padBelowCount)
      rw [sldPadLayerTargetArity]
      exact sldPadWindowTargetArityFrom padAboveCount padBelowCount tailLayers
        (sldLayerTargetArity headLayer)

/-- A padded window composes from the pad-shifted boundary. -/
theorem sldPadWindowIsComposableFrom (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) -> (windowBoundary : Nat) ->
    sldLayersAreComposableFrom windowBoundary windowLayers = true ->
    sldLayersAreComposableFrom (padAboveCount + (windowBoundary + padBelowCount))
      (sldPadWindow padAboveCount padBelowCount windowLayers) = true
  | [], _, _ => rfl
  | headLayer :: tailLayers, windowBoundary, isChainComposable => by
      have doesHeadMatch : sldLayerSourceArity headLayer = windowBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      show (Nat.beq (sldLayerSourceArity (sldPadLayer padAboveCount padBelowCount headLayer))
          (padAboveCount + (windowBoundary + padBelowCount))
        && sldLayersAreComposableFrom
            (sldLayerTargetArity (sldPadLayer padAboveCount padBelowCount headLayer))
            (sldPadWindow padAboveCount padBelowCount tailLayers)) = true
      rw [sldPadLayerSourceArity, doesHeadMatch, beqSelfIsTrue, sldPadLayerTargetArity,
        sldPadWindowIsComposableFrom padAboveCount padBelowCount tailLayers
          (sldLayerTargetArity headLayer) doesTailCompose]
      rfl

/-! ## Mat(N) semantics: per-cell matrices, per-layer direct sums, per-diagram products -/

/-- The generator matrices of [Lafont2003] Section 3, reused from the r1 kit. -/
def sldCellEntries : SldCell -> MatrixEntries
  | SldCell.wire => identityEntries
  | SldCell.generatorMu => addGenEntries
  | SldCell.generatorEta => zeroGenEntries
  | SldCell.generatorDelta => copyGenEntries
  | SldCell.generatorEpsilon => discardGenEntries
  | SldCell.crossing => swapGenEntries

/-- Layer denotation: block-diagonal assembly, top block first ("horizontal composition
corresponds to the direct sum"). -/
def sldLayerEntries : SldLayer -> MatrixEntries
  | [] => identityEntries
  | headCell :: tailCells =>
      directSumEntries (sldCellTargetArity headCell) (sldCellSourceArity headCell)
        (sldCellEntries headCell) (sldLayerEntries tailCells)

/-- Layer-list denotation: matrix product, second stage on the left ("vertical composition
corresponds to the product of matrices"). -/
def sldLayersDenote : List SldLayer -> MatrixEntries
  | [] => identityEntries
  | headLayer :: tailLayers =>
      composeEntries (sldLayerTargetArity headLayer)
        (sldLayersDenote tailLayers) (sldLayerEntries headLayer)

/-- Diagram denotation. -/
def sldDenote (diagram : SldDiagram) : MatrixEntries := sldLayersDenote diagram.layers

/-- The identity diagram denotes the identity matrix ON THE NOSE (definitional). -/
theorem sldIdentityDiagramDenotesIdentity (strandCount : Nat) :
    sldDenote (sldIdentityDiagram strandCount) = identityEntries := rfl

/-! ## The block algebra (pointwise on entries; the old congruence induction, reified) -/

/-- Adding a common left summand preserves order. -/
theorem sldAddLeAddLeft (baseCount : Nat) : {firstNat secondNat : Nat} ->
    firstNat ≤ secondNat -> baseCount + firstNat ≤ baseCount + secondNat := by
  induction baseCount with
  | zero =>
      intro firstNat secondNat isAtMost
      rw [Nat.zero_add, Nat.zero_add]
      exact isAtMost
  | succ basePred inductiveHypothesis =>
      intro firstNat secondNat isAtMost
      rw [Nat.succ_add, Nat.succ_add]
      exact Nat.succ_le_succ (inductiveHypothesis isAtMost)

/-- Adding a common left summand preserves strict order. -/
theorem sldAddLtAddLeft (baseCount : Nat) {firstNat secondNat : Nat}
    (isBelow : firstNat < secondNat) : baseCount + firstNat < baseCount + secondNat :=
  sldAddLeAddLeft baseCount (firstNat := firstNat + 1) (secondNat := secondNat) isBelow

/-- Product congruence: factors agreeing across the middle dimension give equal products. -/
theorem sldProductRespectsEntryAgreement (middleDimension : Nat)
    (afterFirst afterSecond beforeFirst beforeSecond : MatrixEntries) (rowIndex colIndex : Nat)
    (doAfterFactorsAgree : ∀ middleIndex, middleIndex < middleDimension ->
      afterFirst rowIndex middleIndex = afterSecond rowIndex middleIndex)
    (doBeforeFactorsAgree : ∀ middleIndex, middleIndex < middleDimension ->
      beforeFirst middleIndex colIndex = beforeSecond middleIndex colIndex) :
    composeEntries middleDimension afterFirst beforeFirst rowIndex colIndex
      = composeEntries middleDimension afterSecond beforeSecond rowIndex colIndex :=
  sumBelowRespectsPointwise
    (fun middleIndex => afterFirst rowIndex middleIndex * beforeFirst middleIndex colIndex)
    (fun middleIndex => afterSecond rowIndex middleIndex * beforeSecond middleIndex colIndex)
    middleDimension
    (fun middleIndex isMiddleInside => by
      show afterFirst rowIndex middleIndex * beforeFirst middleIndex colIndex
        = afterSecond rowIndex middleIndex * beforeSecond middleIndex colIndex
      rw [doAfterFactorsAgree middleIndex isMiddleInside,
        doBeforeFactorsAgree middleIndex isMiddleInside])

/-- Product associativity, pointwise and unconditional (the sum-exchange dance of the r2
`composeReassociate` case, reified as an entry lemma). -/
theorem sldProductAssocEntry (innerDimension outerDimension : Nat)
    (lastEntries middleEntries firstEntries : MatrixEntries) (rowIndex colIndex : Nat) :
    composeEntries outerDimension lastEntries
        (composeEntries innerDimension middleEntries firstEntries) rowIndex colIndex
      = composeEntries innerDimension
          (composeEntries outerDimension lastEntries middleEntries) firstEntries
          rowIndex colIndex := by
  show sumBelow (fun outerIndex => lastEntries rowIndex outerIndex
      * sumBelow (fun innerIndex => middleEntries outerIndex innerIndex
          * firstEntries innerIndex colIndex) innerDimension) outerDimension
    = sumBelow (fun innerIndex =>
        sumBelow (fun outerIndex => lastEntries rowIndex outerIndex
          * middleEntries outerIndex innerIndex) outerDimension
        * firstEntries innerIndex colIndex) innerDimension
  rw [sumBelowRespectsPointwise
      (fun outerIndex => lastEntries rowIndex outerIndex
        * sumBelow (fun innerIndex => middleEntries outerIndex innerIndex
            * firstEntries innerIndex colIndex) innerDimension)
      (fun outerIndex => sumBelow (fun innerIndex => lastEntries rowIndex outerIndex
        * (middleEntries outerIndex innerIndex * firstEntries innerIndex colIndex))
        innerDimension)
      outerDimension
      (fun outerIndex _ => sumBelowMulLeft (lastEntries rowIndex outerIndex)
        (fun innerIndex => middleEntries outerIndex innerIndex * firstEntries innerIndex colIndex)
        innerDimension),
    sumBelowExchange (fun outerIndex innerIndex => lastEntries rowIndex outerIndex
      * (middleEntries outerIndex innerIndex * firstEntries innerIndex colIndex))
      innerDimension outerDimension]
  exact sumBelowRespectsPointwise _ _ innerDimension
    (fun innerIndex _ => by
      rw [sumBelowMulRight (fun outerIndex => lastEntries rowIndex outerIndex
          * middleEntries outerIndex innerIndex) (firstEntries innerIndex colIndex)
          outerDimension]
      exact sumBelowRespectsPointwise _ _ outerDimension
        (fun outerIndex _ => (mulAssoc (lastEntries rowIndex outerIndex)
          (middleEntries outerIndex innerIndex) (firstEntries innerIndex colIndex)).symm))

/-- Multiplying by the identity on the right (the BEFORE slot) collapses inside the column
rectangle. -/
theorem sldProductWithIdentityBeforeCollapses (middleDimension : Nat)
    (afterEntries : MatrixEntries) (rowIndex colIndex : Nat)
    (isColInside : colIndex < middleDimension) :
    composeEntries middleDimension afterEntries identityEntries rowIndex colIndex
      = afterEntries rowIndex colIndex := by
  refine (sumBelowOfSingleSupport
    (fun middleIndex => afterEntries rowIndex middleIndex * identityEntries middleIndex colIndex)
    middleDimension colIndex isColInside ?_).trans ?_
  · intro middleIndex _ isOffSupport
    show afterEntries rowIndex middleIndex * identityEntries middleIndex colIndex = 0
    rw [identityEntryOffDiagonal isOffSupport]
    rfl
  · show afterEntries rowIndex colIndex * identityEntries colIndex colIndex
      = afterEntries rowIndex colIndex
    rw [identityEntryOnDiagonal colIndex]
    exact mulOneIsSelf (afterEntries rowIndex colIndex)

/-- Multiplying by the identity on the left (the AFTER slot) collapses inside the row
rectangle. -/
theorem sldProductWithIdentityAfterCollapses (middleDimension : Nat)
    (beforeEntries : MatrixEntries) (rowIndex colIndex : Nat)
    (isRowInside : rowIndex < middleDimension) :
    composeEntries middleDimension identityEntries beforeEntries rowIndex colIndex
      = beforeEntries rowIndex colIndex := by
  refine (sumBelowOfSingleSupport
    (fun middleIndex => identityEntries rowIndex middleIndex * beforeEntries middleIndex colIndex)
    middleDimension rowIndex isRowInside ?_).trans ?_
  · intro middleIndex _ isOffSupport
    show identityEntries rowIndex middleIndex * beforeEntries middleIndex colIndex = 0
    rw [identityEntryOffDiagonal (fun isRowAtMiddle => isOffSupport isRowAtMiddle.symm)]
    exact zeroMulIsZero (beforeEntries middleIndex colIndex)
  · show identityEntries rowIndex rowIndex * beforeEntries rowIndex colIndex
      = beforeEntries rowIndex colIndex
    rw [identityEntryOnDiagonal rowIndex]
    exact oneMulIsSelf (beforeEntries rowIndex colIndex)

/-- Direct-sum congruence: blockwise-agreeing entries give equal direct sums (conditional
agreements — the caller supplies exactly what each block needs). -/
theorem sldDirectSumRespectsEntryAgreement (topRowCount topColCount : Nat)
    (topFirst topSecond bottomFirst bottomSecond : MatrixEntries) (rowIndex colIndex : Nat)
    (doTopBlocksAgree : rowIndex < topRowCount -> colIndex < topColCount ->
      topFirst rowIndex colIndex = topSecond rowIndex colIndex)
    (doBottomBlocksAgree : ∀ rowOffset colOffset, rowIndex = topRowCount + rowOffset ->
      colIndex = topColCount + colOffset ->
      bottomFirst rowOffset colOffset = bottomSecond rowOffset colOffset) :
    directSumEntries topRowCount topColCount topFirst bottomFirst rowIndex colIndex
      = directSumEntries topRowCount topColCount topSecond bottomSecond rowIndex colIndex := by
  cases decomposeIndexAgainstBlock topRowCount rowIndex with
  | inl isRowInTop =>
      cases decomposeIndexAgainstBlock topColCount colIndex with
      | inl isColInTop =>
          rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop,
            directSumEntryInTopBlock _ _ isRowInTop isColInTop]
          exact doTopBlocksAgree isRowInTop isColInTop
      | inr colHasOffset =>
          cases colHasOffset with
          | intro colOffset colSplits =>
              rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop,
                directSumEntryInTopRightBlock _ _ colOffset isRowInTop]
  | inr rowHasOffset =>
      cases rowHasOffset with
      | intro rowOffset rowSplits =>
          cases decomposeIndexAgainstBlock topColCount colIndex with
          | inl isColInTop =>
              rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop,
                directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop]
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [rowSplits, colSplits,
                    directSumEntryInBottomBlock _ _ rowOffset colOffset,
                    directSumEntryInBottomBlock _ _ rowOffset colOffset]
                  exact doBottomBlocksAgree rowOffset colOffset rowSplits colSplits

/-- The direct sum of two identity blocks is the identity (pointwise, everywhere). -/
theorem sldDirectSumOfIdentitiesEntry (blockSize : Nat) (rowIndex colIndex : Nat) :
    directSumEntries blockSize blockSize identityEntries identityEntries rowIndex colIndex
      = identityEntries rowIndex colIndex := by
  cases decomposeIndexAgainstBlock blockSize rowIndex with
  | inl isRowInTop =>
      cases decomposeIndexAgainstBlock blockSize colIndex with
      | inl isColInTop => rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop]
      | inr colHasOffset =>
          cases colHasOffset with
          | intro colOffset colSplits =>
              rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop,
                identityEntryOffDiagonal (fun isRowAtOffset => by
                  rw [isRowAtOffset] at isRowInTop
                  exact noLtOfGe (Nat.le_add_right blockSize colOffset) isRowInTop)]
  | inr rowHasOffset =>
      cases rowHasOffset with
      | intro rowOffset rowSplits =>
          cases decomposeIndexAgainstBlock blockSize colIndex with
          | inl isColInTop =>
              rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop,
                identityEntryOffDiagonal (fun isOffsetAtCol => by
                  rw [isOffsetAtCol.symm] at isColInTop
                  exact noLtOfGe (Nat.le_add_right blockSize rowOffset) isColInTop)]
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [rowSplits, colSplits, directSumEntryInBottomBlock _ _ rowOffset colOffset]
                  show cond (Nat.beq rowOffset colOffset) 1 0
                    = cond (Nat.beq (blockSize + rowOffset) (blockSize + colOffset)) 1 0
                  rw [beqAddLeftCancel blockSize rowOffset colOffset]

/-- DIRECT-SUM ASSOCIATIVITY, pointwise and unconditional — the coherence the binary syntax
could not even state cast-free at open arities; here it is an entries computation. -/
theorem sldDirectSumAssocEntry (topRowCount topColCount middleRowCount middleColCount : Nat)
    (topEntries middleEntries bottomEntries : MatrixEntries) (rowIndex colIndex : Nat) :
    directSumEntries topRowCount topColCount topEntries
        (directSumEntries middleRowCount middleColCount middleEntries bottomEntries)
        rowIndex colIndex
      = directSumEntries (topRowCount + middleRowCount) (topColCount + middleColCount)
          (directSumEntries topRowCount topColCount topEntries middleEntries)
          bottomEntries rowIndex colIndex := by
  cases decomposeIndexAgainstBlock topRowCount rowIndex with
  | inl isRowInTop =>
      have isRowInOuterTop : rowIndex < topRowCount + middleRowCount :=
        Nat.le_trans isRowInTop (Nat.le_add_right topRowCount middleRowCount)
      cases decomposeIndexAgainstBlock topColCount colIndex with
      | inl isColInTop =>
          have isColInOuterTop : colIndex < topColCount + middleColCount :=
            Nat.le_trans isColInTop (Nat.le_add_right topColCount middleColCount)
          rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop,
            directSumEntryInTopBlock _ _ isRowInOuterTop isColInOuterTop,
            directSumEntryInTopBlock _ _ isRowInTop isColInTop]
      | inr colHasOffset =>
          cases colHasOffset with
          | intro colOffset colSplits =>
              cases decomposeIndexAgainstBlock middleColCount colOffset with
              | inl isOffsetInMiddleCols =>
                  have isColInOuterTop :
                      topColCount + colOffset < topColCount + middleColCount :=
                    sldAddLtAddLeft topColCount isOffsetInMiddleCols
                  rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop,
                    directSumEntryInTopBlock _ _ isRowInOuterTop isColInOuterTop,
                    directSumEntryInTopRightBlock _ _ colOffset isRowInTop]
              | inr offsetHasOffset =>
                  cases offsetHasOffset with
                  | intro deepColOffset offsetSplits =>
                      rw [colSplits, offsetSplits,
                        directSumEntryInTopRightBlock _ _ (middleColCount + deepColOffset)
                          isRowInTop,
                        (Nat.add_assoc topColCount middleColCount deepColOffset).symm,
                        directSumEntryInTopRightBlock _ _ deepColOffset isRowInOuterTop]
  | inr rowHasOffset =>
      cases rowHasOffset with
      | intro rowOffset rowSplits =>
          cases decomposeIndexAgainstBlock middleRowCount rowOffset with
          | inl isOffsetInMiddleRows =>
              have isRowInOuterTop :
                  topRowCount + rowOffset < topRowCount + middleRowCount :=
                sldAddLtAddLeft topRowCount isOffsetInMiddleRows
              cases decomposeIndexAgainstBlock topColCount colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop,
                    directSumEntryInTopBlock _ _ isRowInOuterTop
                      (Nat.le_trans isColInTop (Nat.le_add_right topColCount middleColCount)),
                    directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      cases decomposeIndexAgainstBlock middleColCount colOffset with
                      | inl isOffsetInMiddleCols =>
                          rw [rowSplits, colSplits,
                            directSumEntryInBottomBlock _ _ rowOffset colOffset,
                            directSumEntryInTopBlock _ _ isRowInOuterTop
                              (sldAddLtAddLeft topColCount isOffsetInMiddleCols),
                            directSumEntryInBottomBlock _ _ rowOffset colOffset,
                            directSumEntryInTopBlock _ _ isOffsetInMiddleRows
                              isOffsetInMiddleCols]
                      | inr offsetHasOffset =>
                          cases offsetHasOffset with
                          | intro deepColOffset offsetSplits =>
                              rw [rowSplits, colSplits, offsetSplits,
                                directSumEntryInBottomBlock _ _ rowOffset
                                  (middleColCount + deepColOffset),
                                directSumEntryInTopRightBlock _ _ deepColOffset
                                  isOffsetInMiddleRows,
                                (Nat.add_assoc topColCount middleColCount deepColOffset).symm,
                                directSumEntryInTopRightBlock _ _ deepColOffset
                                  isRowInOuterTop]
          | inr rowOffsetHasOffset =>
              cases rowOffsetHasOffset with
              | intro deepRowOffset rowOffsetSplits =>
                  cases decomposeIndexAgainstBlock topColCount colIndex with
                  | inl isColInTop =>
                      rw [rowSplits, rowOffsetSplits,
                        directSumEntryInBottomLeftBlock _ _ (middleRowCount + deepRowOffset)
                          isColInTop,
                        (Nat.add_assoc topRowCount middleRowCount deepRowOffset).symm,
                        directSumEntryInBottomLeftBlock _ _ deepRowOffset
                          (Nat.le_trans isColInTop
                            (Nat.le_add_right topColCount middleColCount))]
                  | inr colHasOffset =>
                      cases colHasOffset with
                      | intro colOffset colSplits =>
                          cases decomposeIndexAgainstBlock middleColCount colOffset with
                          | inl isOffsetInMiddleCols =>
                              rw [rowSplits, rowOffsetSplits, colSplits,
                                directSumEntryInBottomBlock _ _
                                  (middleRowCount + deepRowOffset) colOffset,
                                directSumEntryInBottomLeftBlock _ _ deepRowOffset
                                  isOffsetInMiddleCols,
                                (Nat.add_assoc topRowCount middleRowCount deepRowOffset).symm,
                                directSumEntryInBottomLeftBlock _ _ deepRowOffset
                                  (sldAddLtAddLeft topColCount isOffsetInMiddleCols)]
                          | inr offsetHasOffset =>
                              cases offsetHasOffset with
                              | intro deepColOffset offsetSplits =>
                                  rw [rowSplits, rowOffsetSplits, colSplits, offsetSplits,
                                    directSumEntryInBottomBlock _ _
                                      (middleRowCount + deepRowOffset)
                                      (middleColCount + deepColOffset),
                                    directSumEntryInBottomBlock _ _ deepRowOffset deepColOffset,
                                    (Nat.add_assoc topRowCount middleRowCount
                                      deepRowOffset).symm,
                                    (Nat.add_assoc topColCount middleColCount
                                      deepColOffset).symm,
                                    directSumEntryInBottomBlock _ _ deepRowOffset
                                      deepColOffset]

/-- DIRECT-SUM MULTIPLICATIVITY (the pointed-tensor engine, pointwise and unconditional): a
product of block-diagonals is the block-diagonal of the blockwise products. -/
theorem sldDirectSumMultiplicativityEntry
    (topMiddleArity bottomMiddleArity topTargetArity topSourceArity : Nat)
    (topAfter bottomAfter topBefore bottomBefore : MatrixEntries) (rowIndex colIndex : Nat) :
    composeEntries (topMiddleArity + bottomMiddleArity)
        (directSumEntries topTargetArity topMiddleArity topAfter bottomAfter)
        (directSumEntries topMiddleArity topSourceArity topBefore bottomBefore)
        rowIndex colIndex
      = directSumEntries topTargetArity topSourceArity
          (composeEntries topMiddleArity topAfter topBefore)
          (composeEntries bottomMiddleArity bottomAfter bottomBefore) rowIndex colIndex := by
  show sumBelow (fun middleIndex =>
      directSumEntries topTargetArity topMiddleArity topAfter bottomAfter rowIndex middleIndex
      * directSumEntries topMiddleArity topSourceArity topBefore bottomBefore
          middleIndex colIndex)
      (topMiddleArity + bottomMiddleArity)
    = directSumEntries topTargetArity topSourceArity
        (composeEntries topMiddleArity topAfter topBefore)
        (composeEntries bottomMiddleArity bottomAfter bottomBefore) rowIndex colIndex
  simp only [sumBelowSplitsAtBlock]
  cases decomposeIndexAgainstBlock topTargetArity rowIndex with
  | inl isRowInTop =>
      have doesTailVanish : sumBelow (fun offsetIndex =>
          directSumEntries topTargetArity topMiddleArity topAfter bottomAfter rowIndex
            (topMiddleArity + offsetIndex)
          * directSumEntries topMiddleArity topSourceArity topBefore bottomBefore
              (topMiddleArity + offsetIndex) colIndex) bottomMiddleArity = 0 :=
        sumBelowOfAllZeroIsZero _ bottomMiddleArity (fun offsetIndex _ => by
          rw [directSumEntryInTopRightBlock _ _ offsetIndex isRowInTop]
          exact zeroMulIsZero _)
      rw [doesTailVanish, Nat.add_zero]
      cases decomposeIndexAgainstBlock topSourceArity colIndex with
      | inl isColInTop =>
          rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop]
          exact sumBelowRespectsPointwise _ _ topMiddleArity
            (fun middleIndex isMiddleInTop => by
              rw [directSumEntryInTopBlock _ _ isRowInTop isMiddleInTop,
                directSumEntryInTopBlock _ _ isMiddleInTop isColInTop])
      | inr colHasOffset =>
          cases colHasOffset with
          | intro colOffset colSplits =>
              rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop]
              exact sumBelowOfAllZeroIsZero _ topMiddleArity
                (fun middleIndex isMiddleInTop => by
                  rw [directSumEntryInTopRightBlock _ _ colOffset isMiddleInTop]
                  rfl)
  | inr rowHasOffset =>
      cases rowHasOffset with
      | intro rowOffset rowSplits =>
          have doesHeadVanish : sumBelow (fun middleIndex =>
              directSumEntries topTargetArity topMiddleArity topAfter bottomAfter rowIndex
                middleIndex
              * directSumEntries topMiddleArity topSourceArity topBefore bottomBefore
                  middleIndex colIndex) topMiddleArity = 0 :=
            sumBelowOfAllZeroIsZero _ topMiddleArity (fun middleIndex isMiddleInTop => by
              rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isMiddleInTop]
              exact zeroMulIsZero _)
          rw [doesHeadVanish, Nat.zero_add]
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop]
              exact sumBelowOfAllZeroIsZero _ bottomMiddleArity
                (fun offsetIndex _ => by
                  rw [directSumEntryInBottomLeftBlock _ _ offsetIndex isColInTop]
                  rfl)
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [rowSplits, colSplits,
                    directSumEntryInBottomBlock _ _ rowOffset colOffset]
                  exact sumBelowRespectsPointwise _ _ bottomMiddleArity
                    (fun offsetIndex _ => by
                      rw [directSumEntryInBottomBlock _ _ rowOffset offsetIndex,
                        directSumEntryInBottomBlock _ _ offsetIndex colOffset])

/-- A wire layer denotes the identity matrix (pointwise, everywhere). -/
theorem sldWireLayerEntriesAsIdentity : (strandCount rowIndex colIndex : Nat) ->
    sldLayerEntries (sldWireLayerOfArity strandCount) rowIndex colIndex
      = identityEntries rowIndex colIndex
  | 0, _, _ => rfl
  | strandPred + 1, rowIndex, colIndex => by
      show directSumEntries 1 1 identityEntries
          (sldLayerEntries (sldWireLayerOfArity strandPred)) rowIndex colIndex
        = identityEntries rowIndex colIndex
      refine Eq.trans (sldDirectSumRespectsEntryAgreement 1 1 identityEntries identityEntries
        (sldLayerEntries (sldWireLayerOfArity strandPred)) identityEntries rowIndex colIndex
        (fun _ _ => rfl)
        (fun rowOffset colOffset _ _ =>
          sldWireLayerEntriesAsIdentity strandPred rowOffset colOffset)) ?_
      exact sldDirectSumOfIdentitiesEntry 1 rowIndex colIndex

/-- LAYER APPEND IS BLOCK ASSEMBLY (pointwise, everywhere): the entries of an appended layer
are the direct sum of the parts' entries at the parts' fold arities. -/
theorem sldAppendCellsEntriesAsBlocks :
    (firstCells secondCells : SldLayer) -> (rowIndex colIndex : Nat) ->
    sldLayerEntries (sldAppendCells firstCells secondCells) rowIndex colIndex
      = directSumEntries (sldLayerTargetArity firstCells) (sldLayerSourceArity firstCells)
          (sldLayerEntries firstCells) (sldLayerEntries secondCells) rowIndex colIndex
  | [], _, _, _ => rfl
  | headCell :: tailCells, secondCells, rowIndex, colIndex => by
      show directSumEntries (sldCellTargetArity headCell) (sldCellSourceArity headCell)
          (sldCellEntries headCell) (sldLayerEntries (sldAppendCells tailCells secondCells))
          rowIndex colIndex
        = directSumEntries
            (sldCellTargetArity headCell + sldLayerArityBy sldCellTargetArity tailCells)
            (sldCellSourceArity headCell + sldLayerArityBy sldCellSourceArity tailCells)
            (directSumEntries (sldCellTargetArity headCell) (sldCellSourceArity headCell)
              (sldCellEntries headCell) (sldLayerEntries tailCells))
            (sldLayerEntries secondCells) rowIndex colIndex
      refine Eq.trans (sldDirectSumRespectsEntryAgreement (sldCellTargetArity headCell)
        (sldCellSourceArity headCell) (sldCellEntries headCell) (sldCellEntries headCell)
        (sldLayerEntries (sldAppendCells tailCells secondCells))
        (directSumEntries (sldLayerTargetArity tailCells) (sldLayerSourceArity tailCells)
          (sldLayerEntries tailCells) (sldLayerEntries secondCells))
        rowIndex colIndex (fun _ _ => rfl)
        (fun rowOffset colOffset _ _ =>
          sldAppendCellsEntriesAsBlocks tailCells secondCells rowOffset colOffset)) ?_
      exact sldDirectSumAssocEntry (sldCellTargetArity headCell) (sldCellSourceArity headCell)
        (sldLayerTargetArity tailCells) (sldLayerSourceArity tailCells)
        (sldCellEntries headCell) (sldLayerEntries tailCells) (sldLayerEntries secondCells)
        rowIndex colIndex

/-! ## Functoriality 1: denote of append IS the matrix product (unconditional) -/

/-- Denotation of concatenated layer lists is the product of the denotations, pointwise on any
rectangle whose column bound feeds the nil-case identity collapse.  Unconditional — no
composability needed: junk agrees with junk because the middle dimensions are COMPUTED. -/
theorem sldDenoteOfAppendAsProductEntry :
    (firstLayers : List SldLayer) -> (colBoundArity : Nat) -> (secondLayers : List SldLayer) ->
    (rowIndex colIndex : Nat) -> colIndex < colBoundArity ->
    sldLayersDenote (sldAppendLayers firstLayers secondLayers) rowIndex colIndex
      = composeEntries (sldLayersTargetArityFrom colBoundArity firstLayers)
          (sldLayersDenote secondLayers) (sldLayersDenote firstLayers) rowIndex colIndex
  | [], colBoundArity, secondLayers, rowIndex, colIndex, isColInside =>
      (sldProductWithIdentityBeforeCollapses colBoundArity (sldLayersDenote secondLayers)
        rowIndex colIndex isColInside).symm
  | headLayer :: tailLayers, _colBoundArity, secondLayers, rowIndex, colIndex, _ => by
      show composeEntries (sldLayerTargetArity headLayer)
          (sldLayersDenote (sldAppendLayers tailLayers secondLayers))
          (sldLayerEntries headLayer) rowIndex colIndex
        = composeEntries
            (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
            (sldLayersDenote secondLayers)
            (composeEntries (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers)
              (sldLayerEntries headLayer)) rowIndex colIndex
      refine Eq.trans (sldProductRespectsEntryAgreement (sldLayerTargetArity headLayer)
        (sldLayersDenote (sldAppendLayers tailLayers secondLayers))
        (composeEntries (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
          (sldLayersDenote secondLayers) (sldLayersDenote tailLayers))
        (sldLayerEntries headLayer) (sldLayerEntries headLayer) rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldDenoteOfAppendAsProductEntry tailLayers (sldLayerTargetArity headLayer)
            secondLayers rowIndex middleIndex isMiddleInside)
        (fun _ _ => rfl)) ?_
      exact (sldProductAssocEntry (sldLayerTargetArity headLayer)
        (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
        (sldLayersDenote secondLayers) (sldLayersDenote tailLayers)
        (sldLayerEntries headLayer) rowIndex colIndex).symm

/-- Diagram-level Bool form: denote of a composite agrees with the product on any rectangle
over the first diagram's source columns. -/
theorem sldComposeSequentialDenoteAsProduct (firstDiagram secondDiagram : SldDiagram)
    (rowBound : Nat) :
    doEntriesAgreeUpTo rowBound firstDiagram.sourceArity
      (sldDenote (sldComposeSequential firstDiagram secondDiagram))
      (composeEntries (sldTargetArity firstDiagram) (sldDenote secondDiagram)
        (sldDenote firstDiagram)) = true :=
  agreeUpToOfPointwise rowBound firstDiagram.sourceArity _ _
    (fun rowIndex colIndex _ isColInside =>
      sldDenoteOfAppendAsProductEntry firstDiagram.layers firstDiagram.sourceArity
        secondDiagram.layers rowIndex colIndex isColInside)

/-! ## Functoriality 2: denote of the zip tensor IS the direct sum -/

/-- Denotation of an above-padded block is the direct sum with an identity top block
(pointwise on the padded rectangle). -/
theorem sldPadLayersAboveDenoteEntry (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    (rowIndex colIndex : Nat) ->
    rowIndex < padCount + sldLayersTargetArityFrom blockBoundary blockLayers ->
    colIndex < padCount + blockBoundary ->
    sldLayersDenote (sldPadLayersAbove padCount blockLayers) rowIndex colIndex
      = directSumEntries padCount padCount identityEntries (sldLayersDenote blockLayers)
          rowIndex colIndex
  | [], _, _, rowIndex, colIndex, _, _ =>
      (sldDirectSumOfIdentitiesEntry padCount rowIndex colIndex).symm
  | blockHead :: blockTail, blockBoundary, isChainComposable, rowIndex, colIndex,
      isRowInside, isColInside => by
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      show composeEntries
          (sldLayerTargetArity (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
          (sldLayersDenote (sldPadLayersAbove padCount blockTail))
          (sldLayerEntries (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
          rowIndex colIndex
        = directSumEntries padCount padCount identityEntries
            (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
              (sldLayerEntries blockHead)) rowIndex colIndex
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      refine Eq.trans (sldProductRespectsEntryAgreement
        (padCount + sldLayerTargetArity blockHead)
        (sldLayersDenote (sldPadLayersAbove padCount blockTail))
        (directSumEntries padCount padCount identityEntries (sldLayersDenote blockTail))
        (sldLayerEntries (sldAppendCells (sldWireLayerOfArity padCount) blockHead))
        (directSumEntries padCount padCount identityEntries (sldLayerEntries blockHead))
        rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldPadLayersAboveDenoteEntry padCount blockTail (sldLayerTargetArity blockHead)
            doesTailCompose rowIndex middleIndex isRowInside isMiddleInside)
        (fun middleIndex _ => by
          refine Eq.trans (sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padCount)
            blockHead middleIndex colIndex) ?_
          rw [sldWireLayerTargetArity, sldWireLayerSourceArity]
          exact sldDirectSumRespectsEntryAgreement padCount padCount
            (sldLayerEntries (sldWireLayerOfArity padCount)) identityEntries
            (sldLayerEntries blockHead) (sldLayerEntries blockHead) middleIndex colIndex
            (fun _ _ => sldWireLayerEntriesAsIdentity padCount middleIndex colIndex)
            (fun _ _ _ _ => rfl))) ?_
      refine Eq.trans (sldDirectSumMultiplicativityEntry padCount
        (sldLayerTargetArity blockHead) padCount padCount
        identityEntries (sldLayersDenote blockTail) identityEntries
        (sldLayerEntries blockHead) rowIndex colIndex) ?_
      exact sldDirectSumRespectsEntryAgreement padCount padCount
        (composeEntries padCount identityEntries identityEntries) identityEntries
        (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
          (sldLayerEntries blockHead))
        (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
          (sldLayerEntries blockHead))
        rowIndex colIndex
        (fun isRowInPad _ =>
          sldProductWithIdentityAfterCollapses padCount identityEntries rowIndex colIndex
            isRowInPad)
        (fun _ _ _ _ => rfl)

/-- Denotation of a below-padded block is the direct sum with an identity bottom block
(pointwise on the padded rectangle). -/
theorem sldPadLayersBelowDenoteEntry (padCount : Nat) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    (rowIndex colIndex : Nat) ->
    rowIndex < sldLayersTargetArityFrom blockBoundary blockLayers + padCount ->
    colIndex < blockBoundary + padCount ->
    sldLayersDenote (sldPadLayersBelow padCount blockLayers) rowIndex colIndex
      = directSumEntries (sldLayersTargetArityFrom blockBoundary blockLayers) blockBoundary
          (sldLayersDenote blockLayers) identityEntries rowIndex colIndex
  | [], blockBoundary, _, rowIndex, colIndex, _, _ =>
      (sldDirectSumOfIdentitiesEntry blockBoundary rowIndex colIndex).symm
  | blockHead :: blockTail, blockBoundary, isChainComposable, rowIndex, colIndex,
      isRowInside, isColInside => by
      have doesHeadMatch : sldLayerSourceArity blockHead = blockBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      show composeEntries
          (sldLayerTargetArity (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
          (sldLayersDenote (sldPadLayersBelow padCount blockTail))
          (sldLayerEntries (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
          rowIndex colIndex
        = directSumEntries
            (sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail) blockBoundary
            (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
              (sldLayerEntries blockHead)) identityEntries rowIndex colIndex
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      refine Eq.trans (sldProductRespectsEntryAgreement
        (sldLayerTargetArity blockHead + padCount)
        (sldLayersDenote (sldPadLayersBelow padCount blockTail))
        (directSumEntries (sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail)
          (sldLayerTargetArity blockHead) (sldLayersDenote blockTail) identityEntries)
        (sldLayerEntries (sldAppendCells blockHead (sldWireLayerOfArity padCount)))
        (directSumEntries (sldLayerTargetArity blockHead) (sldLayerSourceArity blockHead)
          (sldLayerEntries blockHead) identityEntries)
        rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldPadLayersBelowDenoteEntry padCount blockTail (sldLayerTargetArity blockHead)
            doesTailCompose rowIndex middleIndex isRowInside isMiddleInside)
        (fun middleIndex _ => by
          refine Eq.trans (sldAppendCellsEntriesAsBlocks blockHead
            (sldWireLayerOfArity padCount) middleIndex colIndex) ?_
          exact sldDirectSumRespectsEntryAgreement (sldLayerTargetArity blockHead)
            (sldLayerSourceArity blockHead)
            (sldLayerEntries blockHead) (sldLayerEntries blockHead)
            (sldLayerEntries (sldWireLayerOfArity padCount)) identityEntries
            middleIndex colIndex
            (fun _ _ => rfl)
            (fun rowOffset colOffset _ _ =>
              sldWireLayerEntriesAsIdentity padCount rowOffset colOffset))) ?_
      refine Eq.trans (sldDirectSumMultiplicativityEntry (sldLayerTargetArity blockHead)
        padCount (sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail)
        (sldLayerSourceArity blockHead)
        (sldLayersDenote blockTail) identityEntries
        (sldLayerEntries blockHead) identityEntries rowIndex colIndex) ?_
      refine Eq.trans (sldDirectSumRespectsEntryAgreement
        (sldLayersTargetArityFrom (sldLayerTargetArity blockHead) blockTail)
        (sldLayerSourceArity blockHead)
        (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
          (sldLayerEntries blockHead))
        (composeEntries (sldLayerTargetArity blockHead) (sldLayersDenote blockTail)
          (sldLayerEntries blockHead))
        (composeEntries padCount identityEntries identityEntries) identityEntries
        rowIndex colIndex (fun _ _ => rfl)
        (fun rowOffset colOffset _ doesColSplit => by
          refine sldProductWithIdentityBeforeCollapses padCount identityEntries rowOffset
            colOffset ?_
          rw [doesHeadMatch] at doesColSplit
          rw [doesColSplit] at isColInside
          exact ltOfAddLtAddLeft blockBoundary isColInside)) ?_
      rw [doesHeadMatch]

/-- THE ZIP FUNCTORIALITY: the zip-tensor of composable chains denotes the block-diagonal
direct sum of the chains' denotations (pointwise on the tensor rectangle). -/
theorem sldDenoteOfZipAsDirectSumEntry (topFinalArity bottomFinalArity : Nat) :
    (topLayers bottomLayers : List SldLayer) -> (topBoundary bottomBoundary : Nat) ->
    sldLayersAreComposableFrom topBoundary topLayers = true ->
    sldLayersAreComposableFrom bottomBoundary bottomLayers = true ->
    sldLayersTargetArityFrom topBoundary topLayers = topFinalArity ->
    sldLayersTargetArityFrom bottomBoundary bottomLayers = bottomFinalArity ->
    (rowIndex colIndex : Nat) ->
    rowIndex < topFinalArity + bottomFinalArity ->
    colIndex < topBoundary + bottomBoundary ->
    sldLayersDenote (sldZipLayersWithPads topFinalArity bottomFinalArity topLayers bottomLayers)
        rowIndex colIndex
      = directSumEntries topFinalArity topBoundary
          (sldLayersDenote topLayers) (sldLayersDenote bottomLayers) rowIndex colIndex
  | [], bottomLayers, topBoundary, bottomBoundary, _, isBottomComposable, isTopReached,
      willBottomReach, rowIndex, colIndex, isRowInside, isColInside => by
      have isTopPinned : topBoundary = topFinalArity := isTopReached
      show sldLayersDenote (sldPadLayersAbove topFinalArity bottomLayers) rowIndex colIndex
        = directSumEntries topFinalArity topBoundary identityEntries
            (sldLayersDenote bottomLayers) rowIndex colIndex
      rw [isTopPinned] at isColInside
      rw [isTopPinned]
      refine sldPadLayersAboveDenoteEntry topFinalArity bottomLayers bottomBoundary
        isBottomComposable rowIndex colIndex ?_ isColInside
      rw [willBottomReach]
      exact isRowInside
  | topHead :: topTail, [], topBoundary, bottomBoundary, isTopComposable, _, willTopReach,
      isBottomReached, rowIndex, colIndex, isRowInside, isColInside => by
      have isBottomPinned : bottomBoundary = bottomFinalArity := isBottomReached
      have willTopTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity topHead) topTail = topFinalArity :=
        willTopReach
      show sldLayersDenote (sldPadLayersBelow bottomFinalArity (topHead :: topTail))
          rowIndex colIndex
        = directSumEntries topFinalArity topBoundary
            (sldLayersDenote (topHead :: topTail)) (sldLayersDenote []) rowIndex colIndex
      rw [isBottomPinned] at isColInside
      have paddedForm := sldPadLayersBelowDenoteEntry bottomFinalArity (topHead :: topTail)
        topBoundary isTopComposable rowIndex colIndex
        (by
          have willWholeReach :
              sldLayersTargetArityFrom topBoundary (topHead :: topTail) = topFinalArity :=
            willTopReach
          rw [willWholeReach]
          exact isRowInside)
        isColInside
      refine Eq.trans paddedForm ?_
      have willWholeReach :
          sldLayersTargetArityFrom topBoundary (topHead :: topTail) = topFinalArity :=
        willTopReach
      rw [willWholeReach]
      rfl
  | topHead :: topTail, bottomHead :: bottomTail, topBoundary, bottomBoundary,
      isTopComposable, isBottomComposable, willTopReach, willBottomReach, rowIndex, colIndex,
      isRowInside, isColInside => by
      have doesTopHeadMatch : sldLayerSourceArity topHead = topBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isTopComposable)
      have doesBottomHeadMatch : sldLayerSourceArity bottomHead = bottomBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isBottomComposable)
      have willTopTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity topHead) topTail = topFinalArity :=
        willTopReach
      have willBottomTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity bottomHead) bottomTail
            = bottomFinalArity :=
        willBottomReach
      show composeEntries (sldLayerTargetArity (sldAppendCells topHead bottomHead))
          (sldLayersDenote
            (sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail))
          (sldLayerEntries (sldAppendCells topHead bottomHead)) rowIndex colIndex
        = directSumEntries topFinalArity topBoundary
            (composeEntries (sldLayerTargetArity topHead) (sldLayersDenote topTail)
              (sldLayerEntries topHead))
            (composeEntries (sldLayerTargetArity bottomHead) (sldLayersDenote bottomTail)
              (sldLayerEntries bottomHead)) rowIndex colIndex
      rw [sldAppendCellsTargetArity]
      refine Eq.trans (sldProductRespectsEntryAgreement
        (sldLayerTargetArity topHead + sldLayerTargetArity bottomHead)
        (sldLayersDenote
          (sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail))
        (directSumEntries topFinalArity (sldLayerTargetArity topHead)
          (sldLayersDenote topTail) (sldLayersDenote bottomTail))
        (sldLayerEntries (sldAppendCells topHead bottomHead))
        (directSumEntries (sldLayerTargetArity topHead) (sldLayerSourceArity topHead)
          (sldLayerEntries topHead) (sldLayerEntries bottomHead))
        rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldDenoteOfZipAsDirectSumEntry topFinalArity bottomFinalArity topTail bottomTail
            (sldLayerTargetArity topHead) (sldLayerTargetArity bottomHead)
            (rightIsTrueOfAndTrue isTopComposable) (rightIsTrueOfAndTrue isBottomComposable)
            willTopTailReach willBottomTailReach rowIndex middleIndex isRowInside
            isMiddleInside)
        (fun middleIndex _ =>
          sldAppendCellsEntriesAsBlocks topHead bottomHead middleIndex colIndex)) ?_
      refine Eq.trans (sldDirectSumMultiplicativityEntry (sldLayerTargetArity topHead)
        (sldLayerTargetArity bottomHead) topFinalArity (sldLayerSourceArity topHead)
        (sldLayersDenote topTail) (sldLayersDenote bottomTail)
        (sldLayerEntries topHead) (sldLayerEntries bottomHead) rowIndex colIndex) ?_
      rw [doesTopHeadMatch]

/-- Diagram-level Bool form: denote of a tensor agrees with the direct sum on the tensor
rectangle (given both factors composable). -/
theorem sldTensorParallelDenoteAsDirectSum (topDiagram bottomDiagram : SldDiagram)
    (isTopComposable : sldIsComposable topDiagram = true)
    (isBottomComposable : sldIsComposable bottomDiagram = true) :
    doEntriesAgreeUpTo (sldTargetArity topDiagram + sldTargetArity bottomDiagram)
      (topDiagram.sourceArity + bottomDiagram.sourceArity)
      (sldDenote (sldTensorParallel topDiagram bottomDiagram))
      (directSumEntries (sldTargetArity topDiagram) topDiagram.sourceArity
        (sldDenote topDiagram) (sldDenote bottomDiagram)) = true :=
  agreeUpToOfPointwise _ _ _ _
    (fun rowIndex colIndex isRowInside isColInside =>
      sldDenoteOfZipAsDirectSumEntry (sldTargetArity topDiagram)
        (sldTargetArity bottomDiagram) topDiagram.layers bottomDiagram.layers
        topDiagram.sourceArity bottomDiagram.sourceArity isTopComposable isBottomComposable
        rfl rfl rowIndex colIndex isRowInside isColInside)

/-! ## Defensive fire (3): the Z2 negative control survives the rebuild -/

/-- `delta ; mu` (copy then add — doubles) as a strict-layer diagram. -/
def sldAddAfterCopyDiagram : SldDiagram :=
  { sourceArity := 1, layers := [[SldCell.generatorDelta], [SldCell.generatorMu]] }

/-- `epsilon ; eta` (discard then zero) as a strict-layer diagram. -/
def sldZeroAfterDiscardDiagram : SldDiagram :=
  { sourceArity := 1, layers := [[SldCell.generatorEpsilon], [SldCell.generatorEta]] }

/-- Copy-then-add doubles (kernel computation through the layer semantics). -/
theorem sldAddAfterCopyDenotesDoubling : sldDenote sldAddAfterCopyDiagram 0 0 = 2 := rfl

/-- Discard-then-zero annihilates. -/
theorem sldZeroAfterDiscardDenotesZero : sldDenote sldZeroAfterDiscardDiagram 0 0 = 0 := rfl

/-- DEFENSIVE FIRE (3): the Z2-specific pair STILL SEPARATES over the layer semantics — the
carrier rebuild dissolved the padding anomaly without collapsing Mat(N) (kernel `rfl`). -/
theorem sldZSpecificPairStillSeparates :
    doEntriesAgreeUpTo 1 1 (sldDenote sldAddAfterCopyDiagram)
      (sldDenote sldZeroAfterDiscardDiagram) = false := rfl

/-- Both fire diagrams are composable and boundary-correct (kernel computation). -/
theorem sldFireDiagramsAreWellFormed :
    (sldIsComposable sldCopyDiagram && sldIsComposable sldAddAfterCopyDiagram
      && sldIsComposable sldZeroAfterDiscardDiagram
      && Nat.beq (sldTargetArity sldCopyDiagram) 2
      && Nat.beq (sldTargetArity sldAddAfterCopyDiagram) 1
      && Nat.beq (sldTargetArity sldZeroAfterDiscardDiagram) 1) = true := rfl

/-- The copy diagram denotes the copy matrix on its rectangle (kernel `rfl` consumption of the
layer semantics against the r1 generator table). -/
theorem sldCopyDiagramDenotesCopyGen :
    doEntriesAgreeUpTo 2 1 (sldDenote sldCopyDiagram) copyGenEntries = true := rfl

/-! ## THE MARKER (file-1 half): padding dissolution LANDED

`fxLafontStrictLayer_hasPaddingDissolution` is `true` on the strength of
`sldPaddingDissolvesOnCopy` / `sldPaddingDissolvesOnCopyBelow` (kernel `rfl` — the r3
separator's two sides are the same term) plus the open-diagram forms
`sldTensorWithEmptyTopIsSelf` / `sldTensorWithEmptyBottomIsSelf`.  The embedding-transport
marker lives in the stage-2 file. -/

/-- Stage-D fire (1) marker: the padding hole is DISSOLVED at the carrier level. -/
def fxLafontStrictLayer_hasPaddingDissolution : Bool := true

#eval decide (sldIsComposable (sldTensorParallel (sldIdentityDiagram 0) sldCopyDiagram)
  = sldIsComposable sldCopyDiagram)
#eval decide (sldDenote (sldTensorParallel (sldIdentityDiagram 0) sldCopyDiagram) 1 0
  = sldDenote sldCopyDiagram 1 0)
#eval decide (sldDenote sldAddAfterCopyDiagram 0 0 = 2)
#eval decide (doEntriesAgreeUpTo 1 1 (sldDenote sldAddAfterCopyDiagram)
  (sldDenote sldZeroAfterDiscardDiagram) = false)
#eval decide (sldIsComposable (sldTensorParallel sldCopyDiagram sldAddAfterCopyDiagram) = true)

end FX1Poly.Polygraph.Omega.LafontProp
