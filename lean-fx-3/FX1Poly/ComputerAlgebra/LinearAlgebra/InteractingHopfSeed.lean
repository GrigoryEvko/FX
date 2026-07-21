import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalLinearRelations

/-! # LinearAlgebra/InteractingHopfSeed — the IH_Q presentation seed

The interacting-Hopf-over-Q presentation seed on top of the
`RationalLinearRelations` substrate (prefix `ihq`): strict-layer string diagrams
over the BSZ self-dual signature (Bonchi-Sobocinski-Zanasi, "Interacting Hopf
algebras", arXiv:1403.7048v4 = JPAA 221(1):144-184, 2017, Definition 6.1;
cross-checked against Zanasi's thesis arXiv:1805.03032), an executable
well-formedness gate, the denotation functor into QnfRat generator matrices
(composition = `ihqComposeRows`, parallel layers = the minimal interleaved
tensor built here), the relation set — every Definition 6.1 axiom family as an
(lhs, rhs) diagram pair with a kernel-decided relation-diff gate pin — a
sequential congruence `IhsConv` (refl/symm/trans + rows + prepend/append layer
congruence) with full soundness `ihsConvSound` and the refutation bridge, fires
including false controls, and the unproven completeness statement carrying the
relation census.

Shape follows the F2 template
(`Polygraph/Omega/ZXPhaseFree/SpiderRelationSeed`, prefix `zxp`); carrier and
scalars are QnfRat, so every xor telescope becomes an add/neg/scale telescope
and the scalar boxes `k` / `k-mirror` are genuine cells (over F2 they were
invisible).

`IhsConv` is the sequential-scope congruence: a row/refl/symm/trans core plus
prepend and append layer congruence, contextual in the composition direction.
The gate pins (T3) are complete: all 46 relation rows fire the span decision by
`rfl`.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfSeed.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — small executable helpers and cast lemmas -/

/-- Structural Bool equality on `Nat` (fresh, per the seed's self-containment). -/
def ihsNatEqB : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, _secondPred + 1 => false
  | _firstPred + 1, 0 => false
  | firstPred + 1, secondPred + 1 => ihsNatEqB firstPred secondPred

theorem ihsNatEqBSound : (firstValue secondValue : Nat) ->
    ihsNatEqB firstValue secondValue = true -> firstValue = secondValue
  | 0, 0, _hCheck => rfl
  | 0, _secondPred + 1, hCheck => Bool.noConfusion hCheck
  | _firstPred + 1, 0, hCheck => Bool.noConfusion hCheck
  | firstPred + 1, secondPred + 1, hCheck =>
      congrArg (fun innerValue => innerValue + 1)
        (ihsNatEqBSound firstPred secondPred hCheck)

/-- Structural Bool conjunction (fresh; keeps the gate self-contained). -/
def ihsAndB : Bool -> Bool -> Bool
  | true, secondFlag => secondFlag
  | false, _secondFlag => false

theorem ihsAndBTrueLeft : (leftFlag rightFlag : Bool) ->
    ihsAndB leftFlag rightFlag = true -> leftFlag = true
  | true, _rightFlag, _hBoth => rfl
  | false, _rightFlag, hBoth => Bool.noConfusion hBoth

theorem ihsAndBTrueRight : (leftFlag rightFlag : Bool) ->
    ihsAndB leftFlag rightFlag = true -> rightFlag = true
  | true, _rightFlag, hBoth => hBoth
  | false, _rightFlag, hBoth => Bool.noConfusion hBoth

/-- A zero-length coefficient row is the empty row. -/
theorem ihsLengthZeroNil : (row : List QnfRat) -> row.length = 0 -> row = []
  | [], _hLen => rfl
  | _headCoeff :: _restCoeffs, hLen => nomatch hLen

/-- Width-index transport for `IhqAllWidth`. -/
theorem ihsAllWidthCast {firstWidth secondWidth : Nat} {rows : List (List QnfRat)}
    (hWidthEq : firstWidth = secondWidth) (hAll : IhqAllWidth firstWidth rows) :
    IhqAllWidth secondWidth rows := by
  rw [<- hWidthEq]
  exact hAll

/-! ## Stage 1 — the IH_Q cells (T1)

The BSZ self-dual signature, Definition 6.1 / the pushout (Top) of Section 6:
the four HA_Q generators, their four HA_Q^op mirrors, the scalar box for every
`k : QnfRat` in both orientations, plus the PROP plumbing cells (wire,
adjacent crossing).  Mirrors are explicit cells (not derived converses at the
syntax level); the sanity pins `ihsMirror*IsConverse` verify that each mirror's
generator matrix is literally `ihqConverseRows` of its partner's.

Generator table (census section 1):
  G1 add       = `whiteMult`        2 -> 1   G5 coadd     = `whiteComult`  1 -> 2
  G2 zero      = `whiteUnit`        0 -> 1   G6 cozero    = `whiteCounit`  1 -> 0
  G3 copy      = `blackComult`      1 -> 2   G7 cocopy    = `blackMult`    2 -> 1
  G4 discard   = `blackCounit`      1 -> 0   G8 blackunit = `blackUnit`    0 -> 1
  G9 scalar k  = `scalarBox k`      1 -> 1   G10 mirror k = `scalarBoxMirror k`
Not cells: antipode (:= `scalarBox (-1)`, Remark 3.4), cups/caps (defined
circuits, Section 5.1). -/

/-- IH_Q diagram cells over the self-dual signature (see the stage docstring). -/
inductive IhsCell : Type where
  | whiteMult : IhsCell
  | whiteUnit : IhsCell
  | blackComult : IhsCell
  | blackCounit : IhsCell
  | whiteComult : IhsCell
  | whiteCounit : IhsCell
  | blackMult : IhsCell
  | blackUnit : IhsCell
  | scalarBox : QnfRat -> IhsCell
  | scalarBoxMirror : QnfRat -> IhsCell
  | wire : IhsCell
  | crossing : IhsCell

def ihsCellDomArity : IhsCell -> Nat
  | IhsCell.whiteMult => 2
  | IhsCell.whiteUnit => 0
  | IhsCell.blackComult => 1
  | IhsCell.blackCounit => 1
  | IhsCell.whiteComult => 1
  | IhsCell.whiteCounit => 1
  | IhsCell.blackMult => 2
  | IhsCell.blackUnit => 0
  | IhsCell.scalarBox _scalarValue => 1
  | IhsCell.scalarBoxMirror _scalarValue => 1
  | IhsCell.wire => 1
  | IhsCell.crossing => 2

def ihsCellCodArity : IhsCell -> Nat
  | IhsCell.whiteMult => 1
  | IhsCell.whiteUnit => 1
  | IhsCell.blackComult => 2
  | IhsCell.blackCounit => 0
  | IhsCell.whiteComult => 2
  | IhsCell.whiteCounit => 0
  | IhsCell.blackMult => 1
  | IhsCell.blackUnit => 1
  | IhsCell.scalarBox _scalarValue => 1
  | IhsCell.scalarBoxMirror _scalarValue => 1
  | IhsCell.wire => 1
  | IhsCell.crossing => 2

/-- Generator matrix of each cell over width `dom + cod` (domain block first).
LinRel_Q semantics per the census: add `{((a,b), a+b)}`, zero `{((), 0)}` (the
empty generator list, i.e. the zero subspace), copy `{(a,(a,a))}`, discard
`{(a,())}` (the full line), scalar `k` `{(x, kx)}`; mirrors are the relational
converses (block-swapped matrices). -/
def ihsCellRows : IhsCell -> List (List QnfRat)
  | IhsCell.whiteMult => [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
  | IhsCell.whiteUnit => []
  | IhsCell.blackComult => [[qnfOne, qnfOne, qnfOne]]
  | IhsCell.blackCounit => [[qnfOne]]
  | IhsCell.whiteComult => [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
  | IhsCell.whiteCounit => []
  | IhsCell.blackMult => [[qnfOne, qnfOne, qnfOne]]
  | IhsCell.blackUnit => [[qnfOne]]
  | IhsCell.scalarBox scalarValue => [[qnfOne, scalarValue]]
  | IhsCell.scalarBoxMirror scalarValue => [[scalarValue, qnfOne]]
  | IhsCell.wire => [[qnfOne, qnfOne]]
  | IhsCell.crossing =>
      [[qnfOne, qnfZero, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne, qnfZero]]

theorem ihsCellRowsWidth : (cell : IhsCell) ->
    IhqAllWidth (ihsCellDomArity cell + ihsCellCodArity cell) (ihsCellRows cell)
  | IhsCell.whiteMult => IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)
  | IhsCell.whiteUnit => IhqAllWidth.nil
  | IhsCell.blackComult => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.blackCounit => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.whiteComult => IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)
  | IhsCell.whiteCounit => IhqAllWidth.nil
  | IhsCell.blackMult => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.blackUnit => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.scalarBox _scalarValue => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.scalarBoxMirror _scalarValue => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.wire => IhqAllWidth.cons rfl IhqAllWidth.nil
  | IhsCell.crossing => IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)

/-! ### Small named scalars for the row instances -/

def ihsScalarTwo : QnfRat := qnfOfInt 2
def ihsScalarThree : QnfRat := qnfOfInt 3
def ihsScalarFive : QnfRat := qnfOfInt 5
def ihsScalarSix : QnfRat := qnfOfInt 6

/-- The antipode is the scalar `-1` box (BSZ Remark 3.4), never a primitive cell. -/
def ihsAntipodeScalar : QnfRat := qnfOfInt (-1)

/-! ### Mirror sanity pins: each mirror's matrix is the literal block-swap
(`ihqConverseRows`) of its partner's -/

theorem ihsMirrorCoaddIsConverseOfAdd :
    ihsCellRows IhsCell.whiteComult
      = ihqConverseRows 2 (ihsCellRows IhsCell.whiteMult) := rfl

theorem ihsMirrorCocopyIsConverseOfCopy :
    ihsCellRows IhsCell.blackMult
      = ihqConverseRows 1 (ihsCellRows IhsCell.blackComult) := rfl

theorem ihsMirrorBlackUnitIsConverseOfDiscard :
    ihsCellRows IhsCell.blackUnit
      = ihqConverseRows 1 (ihsCellRows IhsCell.blackCounit) := rfl

theorem ihsMirrorCozeroIsConverseOfZero :
    ihsCellRows IhsCell.whiteCounit
      = ihqConverseRows 0 (ihsCellRows IhsCell.whiteUnit) := rfl

theorem ihsMirrorScalarTwoIsConverse :
    ihsCellRows (IhsCell.scalarBoxMirror ihsScalarTwo)
      = ihqConverseRows 1 (ihsCellRows (IhsCell.scalarBox ihsScalarTwo)) := rfl

/-! ## Stage 2 — the minimal layer tensor (T2 support)

Interleaved direct sum of generator matrices (domain blocks together, then
codomain blocks), built on `ihqCat`/`ihqZeroRow`.  The definition and its width
lemma are shipped here. -/

/-- Embed a first-factor row `(x1 | y1)` as `(x1, 0, y1, 0)`. -/
def ihsTensorEmbedFirst (firstDomWidth secondDomWidth secondCodWidth : Nat)
    (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (ihqTakeN firstDomWidth rowPair)
    (ihqCat (ihqZeroRow secondDomWidth)
      (ihqCat (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth)))

/-- Embed a second-factor row `(x2 | y2)` as `(0, x2, 0, y2)`. -/
def ihsTensorEmbedSecond (firstDomWidth secondDomWidth firstCodWidth : Nat)
    (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (ihqZeroRow firstDomWidth)
    (ihqCat (ihqTakeN secondDomWidth rowPair)
      (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair)))

/-- Tensor (interleaved direct sum) of generator matrices. -/
def ihsTensorRows (firstDomWidth firstCodWidth secondDomWidth secondCodWidth : Nat)
    (firstRows secondRows : List (List QnfRat)) : List (List QnfRat) :=
  ihqCatRows
    (ihqMapRows (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth)
      firstRows)
    (ihqMapRows (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth)
      secondRows)

theorem ihsTensorRowsWidth (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : IhqAllWidth (secondDomWidth + secondCodWidth) secondRows) :
    IhqAllWidth ((firstDomWidth + secondDomWidth) + (firstCodWidth + secondCodWidth))
      (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows) := by
  refine ihsAllWidthCast
    (Nat.add_assoc firstDomWidth secondDomWidth
      (firstCodWidth + secondCodWidth)).symm ?_
  refine ihqCatRowsWidth _ _ ?_ ?_
  · refine ihqMapRowsWidth _ ?_ firstRows hFirstAll
    intro rowPair hRowLen
    show (ihqCat (ihqTakeN firstDomWidth rowPair)
        (ihqCat (ihqZeroRow secondDomWidth)
          (ihqCat (ihqDropN firstDomWidth rowPair)
            (ihqZeroRow secondCodWidth)))).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
    rw [ihqCatLength, ihqCatLength, ihqCatLength,
      ihqTakeNLength rowPair firstDomWidth firstCodWidth hRowLen,
      ihqDropNLength rowPair firstDomWidth firstCodWidth hRowLen,
      ihqZeroRowLength, ihqZeroRowLength]
  · refine ihqMapRowsWidth _ ?_ secondRows hSecondAll
    intro rowPair hRowLen
    show (ihqCat (ihqZeroRow firstDomWidth)
        (ihqCat (ihqTakeN secondDomWidth rowPair)
          (ihqCat (ihqZeroRow firstCodWidth)
            (ihqDropN secondDomWidth rowPair)))).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
    rw [ihqCatLength, ihqCatLength, ihqCatLength,
      ihqTakeNLength rowPair secondDomWidth secondCodWidth hRowLen,
      ihqDropNLength rowPair secondDomWidth secondCodWidth hRowLen,
      ihqZeroRowLength, ihqZeroRowLength]

/-! ## Stage 3 — strict layers and the diagram carrier (T1/T2) -/

def ihsLayerDomArity : List IhsCell -> Nat
  | [] => 0
  | headCell :: restCells => ihsCellDomArity headCell + ihsLayerDomArity restCells

def ihsLayerCodArity : List IhsCell -> Nat
  | [] => 0
  | headCell :: restCells => ihsCellCodArity headCell + ihsLayerCodArity restCells

/-- Layer denotation: iterated interleaved direct sum, head cell first. -/
def ihsLayerDenote : List IhsCell -> List (List QnfRat)
  | [] => []
  | headCell :: restCells =>
      ihsTensorRows (ihsCellDomArity headCell) (ihsCellCodArity headCell)
        (ihsLayerDomArity restCells) (ihsLayerCodArity restCells)
        (ihsCellRows headCell) (ihsLayerDenote restCells)

theorem ihsLayerDenoteWidth : (layer : List IhsCell) ->
    IhqAllWidth (ihsLayerDomArity layer + ihsLayerCodArity layer)
      (ihsLayerDenote layer)
  | [] => IhqAllWidth.nil
  | headCell :: restCells =>
      ihsTensorRowsWidth (ihsCellDomArity headCell) (ihsCellCodArity headCell)
        (ihsLayerDomArity restCells) (ihsLayerCodArity restCells)
        (ihsCellRows headCell) (ihsLayerDenote restCells)
        (ihsCellRowsWidth headCell) (ihsLayerDenoteWidth restCells)

/-- Output arity after running the layer list from the given input arity. -/
def ihsLayersCodArity : Nat -> List (List IhsCell) -> Nat
  | currentArity, [] => currentArity
  | _currentArity, layer :: restLayers =>
      ihsLayersCodArity (ihsLayerCodArity layer) restLayers

/-- Well-formedness of a layer list against a running arity. -/
inductive IhsLayersWF : Nat -> List (List IhsCell) -> Prop where
  | nil (currentArity : Nat) : IhsLayersWF currentArity []
  | cons {currentArity : Nat} {layer : List IhsCell}
      {restLayers : List (List IhsCell)}
      (hDom : ihsLayerDomArity layer = currentArity)
      (hRest : IhsLayersWF (ihsLayerCodArity layer) restLayers) :
      IhsLayersWF currentArity (layer :: restLayers)

/-- Arity-index transport for `IhsLayersWF`. -/
theorem ihsLayersWFCast {firstArity secondArity : Nat}
    {layers : List (List IhsCell)} (hArityEq : firstArity = secondArity)
    (hWF : IhsLayersWF firstArity layers) : IhsLayersWF secondArity layers := by
  rw [<- hArityEq]
  exact hWF

/-- Denotation of a layer list: iterated relational composition. -/
def ihsLayersDenote : Nat -> List (List IhsCell) -> List (List QnfRat)
  | currentArity, [] => ihqIdRows currentArity
  | currentArity, layer :: restLayers =>
      ihqComposeRows currentArity (ihsLayerCodArity layer)
        (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
        (ihsLayerDenote layer)
        (ihsLayersDenote (ihsLayerCodArity layer) restLayers)

theorem ihsLayersDenoteWidth : {currentArity : Nat} ->
    (layers : List (List IhsCell)) -> IhsLayersWF currentArity layers ->
    IhqAllWidth (currentArity + ihsLayersCodArity currentArity layers)
      (ihsLayersDenote currentArity layers)
  | currentArity, [], _hWF => ihqIdRowsWidth currentArity
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          exact ihqComposeRowsWidth currentArity (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            (ihsLayerDenote layer)
            (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            (ihsAllWidthCast
              (congrArg (fun boundaryArity =>
                boundaryArity + ihsLayerCodArity layer) hDom)
              (ihsLayerDenoteWidth layer))
            (ihsLayersDenoteWidth restLayers hRest)

/-- The diagram carrier: a source arity plus a layer list. -/
structure IhsDiagram where
  sourceArity : Nat
  layers : List (List IhsCell)

def ihsDiagramCodArity (diagram : IhsDiagram) : Nat :=
  ihsLayersCodArity diagram.sourceArity diagram.layers

def IhsDiagramWF (diagram : IhsDiagram) : Prop :=
  IhsLayersWF diagram.sourceArity diagram.layers

def ihsDiagramDenote (diagram : IhsDiagram) : List (List QnfRat) :=
  ihsLayersDenote diagram.sourceArity diagram.layers

theorem ihsDiagramDenoteWidth (diagram : IhsDiagram) (hWF : IhsDiagramWF diagram) :
    IhqAllWidth (diagram.sourceArity + ihsDiagramCodArity diagram)
      (ihsDiagramDenote diagram) :=
  ihsLayersDenoteWidth diagram.layers hWF

/-- Executable well-formedness of a layer list (the arity check). -/
def ihsLayersWFB : Nat -> List (List IhsCell) -> Bool
  | _currentArity, [] => true
  | currentArity, layer :: restLayers =>
      match ihsNatEqB (ihsLayerDomArity layer) currentArity with
      | true => ihsLayersWFB (ihsLayerCodArity layer) restLayers
      | false => false

theorem ihsLayersWFOfB : (currentArity : Nat) -> (layers : List (List IhsCell)) ->
    ihsLayersWFB currentArity layers = true -> IhsLayersWF currentArity layers
  | currentArity, [], _hCheck => IhsLayersWF.nil currentArity
  | currentArity, layer :: restLayers, hCheck => by
      cases hArityCheck : ihsNatEqB (ihsLayerDomArity layer) currentArity with
      | false =>
          rw [show ihsLayersWFB currentArity (layer :: restLayers)
              = match ihsNatEqB (ihsLayerDomArity layer) currentArity with
                | true => ihsLayersWFB (ihsLayerCodArity layer) restLayers
                | false => false from rfl,
            hArityCheck] at hCheck
          exact Bool.noConfusion hCheck
      | true =>
          rw [show ihsLayersWFB currentArity (layer :: restLayers)
              = match ihsNatEqB (ihsLayerDomArity layer) currentArity with
                | true => ihsLayersWFB (ihsLayerCodArity layer) restLayers
                | false => false from rfl,
            hArityCheck] at hCheck
          exact IhsLayersWF.cons (ihsNatEqBSound _ _ hArityCheck)
            (ihsLayersWFOfB (ihsLayerCodArity layer) restLayers hCheck)

/-- Executable diagram well-formedness. -/
def ihsDiagramWFB (diagram : IhsDiagram) : Bool :=
  ihsLayersWFB diagram.sourceArity diagram.layers

theorem ihsDiagramWFOfB (diagram : IhsDiagram)
    (hCheck : ihsDiagramWFB diagram = true) : IhsDiagramWF diagram :=
  ihsLayersWFOfB diagram.sourceArity diagram.layers hCheck

/-! ## Stage 4 — relation equivalence and the span bridges -/

/-- Two generator matrices present the SAME relation at the given boundary. -/
def IhsRelEquiv (domWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat)) : Prop :=
  (domVec codVec : List QnfRat) ->
    (IhqPairMem domWidth codWidth firstRows domVec codVec
      <-> IhqPairMem domWidth codWidth secondRows domVec codVec)

theorem ihsRelEquivRefl (domWidth codWidth : Nat) (rows : List (List QnfRat)) :
    IhsRelEquiv domWidth codWidth rows rows :=
  fun _domVec _codVec => Iff.rfl

theorem ihsRelEquivSymm {domWidth codWidth : Nat}
    {firstRows secondRows : List (List QnfRat)}
    (hEquiv : IhsRelEquiv domWidth codWidth firstRows secondRows) :
    IhsRelEquiv domWidth codWidth secondRows firstRows :=
  fun domVec codVec => (hEquiv domVec codVec).symm

theorem ihsRelEquivTrans {domWidth codWidth : Nat}
    {firstRows secondRows thirdRows : List (List QnfRat)}
    (hFirst : IhsRelEquiv domWidth codWidth firstRows secondRows)
    (hSecond : IhsRelEquiv domWidth codWidth secondRows thirdRows) :
    IhsRelEquiv domWidth codWidth firstRows thirdRows :=
  fun domVec codVec => Iff.trans (hFirst domVec codVec) (hSecond domVec codVec)

theorem ihsRelEquivCast {domWidth domWidth2 codWidth codWidth2 : Nat}
    {firstRows secondRows : List (List QnfRat)} (hDomEq : domWidth = domWidth2)
    (hCodEq : codWidth = codWidth2)
    (hEquiv : IhsRelEquiv domWidth codWidth firstRows secondRows) :
    IhsRelEquiv domWidth2 codWidth2 firstRows secondRows := by
  rw [<- hDomEq, <- hCodEq]
  exact hEquiv

theorem ihsRelEquivOfSpanIff {domWidth codWidth : Nat}
    {firstRows secondRows : List (List QnfRat)}
    (hIff : (vector : List QnfRat) ->
      (IhqMemSpan (domWidth + codWidth) firstRows vector
        <-> IhqMemSpan (domWidth + codWidth) secondRows vector)) :
    IhsRelEquiv domWidth codWidth firstRows secondRows := by
  intro domVec codVec
  refine Iff.intro ?_ ?_
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      ((hIff (ihqCat domVec codVec)).mp hPair.right.right))
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      ((hIff (ihqCat domVec codVec)).mpr hPair.right.right))

theorem ihsSpanIffOfRelEquiv {domWidth codWidth : Nat}
    {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : IhqAllWidth (domWidth + codWidth) secondRows)
    (hEquiv : IhsRelEquiv domWidth codWidth firstRows secondRows)
    (vector : List QnfRat) :
    IhqMemSpan (domWidth + codWidth) firstRows vector
      <-> IhqMemSpan (domWidth + codWidth) secondRows vector := by
  refine Iff.intro ?_ ?_
  · intro hMem
    have hVecLen := ihqMemSpanWidth hFirstAll hMem
    have hSplitBack := ihqCatTakeDrop vector domWidth codWidth hVecLen
    have hPair : IhqPairMem domWidth codWidth firstRows (ihqTakeN domWidth vector)
        (ihqDropN domWidth vector) := by
      refine And.intro (ihqTakeNLength vector domWidth codWidth hVecLen)
        (And.intro (ihqDropNLength vector domWidth codWidth hVecLen) ?_)
      rw [hSplitBack]
      exact hMem
    have hOther := (hEquiv (ihqTakeN domWidth vector)
      (ihqDropN domWidth vector)).mp hPair
    have hOtherMem := hOther.right.right
    rw [hSplitBack] at hOtherMem
    exact hOtherMem
  · intro hMem
    have hVecLen := ihqMemSpanWidth hSecondAll hMem
    have hSplitBack := ihqCatTakeDrop vector domWidth codWidth hVecLen
    have hPair : IhqPairMem domWidth codWidth secondRows (ihqTakeN domWidth vector)
        (ihqDropN domWidth vector) := by
      refine And.intro (ihqTakeNLength vector domWidth codWidth hVecLen)
        (And.intro (ihqDropNLength vector domWidth codWidth hVecLen) ?_)
      rw [hSplitBack]
      exact hMem
    have hOther := (hEquiv (ihqTakeN domWidth vector)
      (ihqDropN domWidth vector)).mpr hPair
    have hOtherMem := hOther.right.right
    rw [hSplitBack] at hOtherMem
    exact hOtherMem

/-- Bool decision -> relation equivalence (the working direction of every fire). -/
theorem ihsRelEquivOfSpanEqB {domWidth codWidth : Nat}
    {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : IhqAllWidth (domWidth + codWidth) secondRows)
    (hEq : ihqSpanEqB firstRows secondRows = true) :
    IhsRelEquiv domWidth codWidth firstRows secondRows :=
  ihsRelEquivOfSpanIff
    (fun vector => ihqSpanEqBSound hFirstAll hSecondAll hEq vector)

/-- Relation equivalence -> Bool decision (the refutation direction). -/
theorem ihsSpanEqBOfRelEquiv {domWidth codWidth : Nat}
    {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : IhqAllWidth (domWidth + codWidth) secondRows)
    (hEquiv : IhsRelEquiv domWidth codWidth firstRows secondRows) :
    ihqSpanEqB firstRows secondRows = true :=
  ihqSpanEqBComplete hFirstAll hSecondAll
    (fun vector => ihsSpanIffOfRelEquiv hFirstAll hSecondAll hEquiv vector)

/-! ## Stage 5 — the identity spec (`ihqIdRows` denotes the diagonal) -/

/-- `ihqPadPairRow` maps the zero row to the zero row. -/
theorem ihsPadPairRowZero (halfWidth : Nat) :
    ihqPadPairRow halfWidth (ihqZeroRow (halfWidth + halfWidth))
      = ihqZeroRow ((halfWidth + 1) + (halfWidth + 1)) := by
  show ihqCat (qnfZero :: ihqTakeN halfWidth (ihqZeroRow (halfWidth + halfWidth)))
      (qnfZero :: ihqDropN halfWidth (ihqZeroRow (halfWidth + halfWidth)))
    = ihqZeroRow ((halfWidth + 1) + (halfWidth + 1))
  rw [ihqTakeNZeroRowExact halfWidth halfWidth,
    ihqDropNZeroRowExact halfWidth halfWidth]
  exact ihqCatZeroZero (halfWidth + 1) (halfWidth + 1)

/-- `ihqPadPairRow` commutes with row addition (at the exact width). -/
theorem ihsPadPairRowAdd (halfWidth : Nat) (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = halfWidth + halfWidth)
    (hSecondLen : secondPair.length = halfWidth + halfWidth) :
    ihqPadPairRow halfWidth (ihqRowAdd firstPair secondPair)
      = ihqRowAdd (ihqPadPairRow halfWidth firstPair)
          (ihqPadPairRow halfWidth secondPair) := by
  have hTakeLens : (qnfZero :: ihqTakeN halfWidth firstPair).length
      = (qnfZero :: ihqTakeN halfWidth secondPair).length := by
    show (ihqTakeN halfWidth firstPair).length + 1
      = (ihqTakeN halfWidth secondPair).length + 1
    rw [ihqTakeNLength firstPair halfWidth halfWidth hFirstLen,
      ihqTakeNLength secondPair halfWidth halfWidth hSecondLen]
  show ihqCat (qnfZero :: ihqTakeN halfWidth (ihqRowAdd firstPair secondPair))
      (qnfZero :: ihqDropN halfWidth (ihqRowAdd firstPair secondPair))
    = ihqRowAdd
        (ihqCat (qnfZero :: ihqTakeN halfWidth firstPair)
          (qnfZero :: ihqDropN halfWidth firstPair))
        (ihqCat (qnfZero :: ihqTakeN halfWidth secondPair)
          (qnfZero :: ihqDropN halfWidth secondPair))
  rw [ihqTakeNAdd halfWidth firstPair secondPair,
    ihqDropNAdd halfWidth firstPair secondPair,
    ihqRowAddCat (qnfZero :: ihqTakeN halfWidth firstPair)
      (qnfZero :: ihqDropN halfWidth firstPair)
      (qnfZero :: ihqTakeN halfWidth secondPair)
      (qnfZero :: ihqDropN halfWidth secondPair) hTakeLens]
  show ihqCat
      (qnfZero :: ihqRowAdd (ihqTakeN halfWidth firstPair)
        (ihqTakeN halfWidth secondPair))
      (qnfZero :: ihqRowAdd (ihqDropN halfWidth firstPair)
        (ihqDropN halfWidth secondPair))
    = ihqCat
        (qnfAdd qnfZero qnfZero
          :: ihqRowAdd (ihqTakeN halfWidth firstPair)
            (ihqTakeN halfWidth secondPair))
        (qnfAdd qnfZero qnfZero
          :: ihqRowAdd (ihqDropN halfWidth firstPair)
            (ihqDropN halfWidth secondPair))
  rw [qnfAddZeroLeft qnfZero]

/-- `ihqPadPairRow` commutes with scaling. -/
theorem ihsPadPairRowScale (halfWidth : Nat) (scalar : QnfRat)
    (rowPair : List QnfRat) :
    ihqPadPairRow halfWidth (ihqRowScale scalar rowPair)
      = ihqRowScale scalar (ihqPadPairRow halfWidth rowPair) := by
  show ihqCat (qnfZero :: ihqTakeN halfWidth (ihqRowScale scalar rowPair))
      (qnfZero :: ihqDropN halfWidth (ihqRowScale scalar rowPair))
    = ihqRowScale scalar
        (ihqCat (qnfZero :: ihqTakeN halfWidth rowPair)
          (qnfZero :: ihqDropN halfWidth rowPair))
  rw [ihqTakeNScale scalar halfWidth rowPair, ihqDropNScale scalar halfWidth rowPair,
    ihqRowScaleCat scalar (qnfZero :: ihqTakeN halfWidth rowPair)
      (qnfZero :: ihqDropN halfWidth rowPair)]
  show ihqCat (qnfZero :: ihqRowScale scalar (ihqTakeN halfWidth rowPair))
      (qnfZero :: ihqRowScale scalar (ihqDropN halfWidth rowPair))
    = ihqCat (qnfMul scalar qnfZero :: ihqRowScale scalar (ihqTakeN halfWidth rowPair))
        (qnfMul scalar qnfZero :: ihqRowScale scalar (ihqDropN halfWidth rowPair))
  rw [grqQnfMulZeroRight scalar]

/-- Combining the head identity generator (scaled) with a padded pair:
`s * (1,0..|1,0..) + (0,f|0,b) = (s,f|s,b)`. -/
theorem ihsIdHeadCombine (widthPred : Nat) (headScalar : QnfRat)
    (frontPart backPart : List QnfRat)
    (hFrontLen : frontPart.length = widthPred)
    (hBackLen : backPart.length = widthPred) :
    ihqRowAdd
        (ihqRowScale headScalar
          (ihqCat (qnfOne :: ihqZeroRow widthPred) (qnfOne :: ihqZeroRow widthPred)))
        (ihqCat (qnfZero :: frontPart) (qnfZero :: backPart))
      = ihqCat (headScalar :: frontPart) (headScalar :: backPart) := by
  have hScaleHead : ihqRowScale headScalar
      (ihqCat (qnfOne :: ihqZeroRow widthPred) (qnfOne :: ihqZeroRow widthPred))
      = ihqCat (headScalar :: ihqZeroRow widthPred)
          (headScalar :: ihqZeroRow widthPred) := by
    rw [ihqRowScaleCat headScalar (qnfOne :: ihqZeroRow widthPred)
      (qnfOne :: ihqZeroRow widthPred)]
    show ihqCat
        (qnfMul headScalar qnfOne :: ihqRowScale headScalar (ihqZeroRow widthPred))
        (qnfMul headScalar qnfOne :: ihqRowScale headScalar (ihqZeroRow widthPred))
      = ihqCat (headScalar :: ihqZeroRow widthPred)
          (headScalar :: ihqZeroRow widthPred)
    rw [qnfMulOneRight headScalar, ihqRowScaleZeroRow headScalar widthPred]
  have hHeadLens : (headScalar :: ihqZeroRow widthPred).length
      = (qnfZero :: frontPart).length := by
    show (ihqZeroRow widthPred).length + 1 = frontPart.length + 1
    rw [ihqZeroRowLength widthPred, hFrontLen]
  rw [hScaleHead,
    ihqRowAddCat (headScalar :: ihqZeroRow widthPred)
      (headScalar :: ihqZeroRow widthPred) (qnfZero :: frontPart)
      (qnfZero :: backPart) hHeadLens]
  show ihqCat
      (qnfAdd headScalar qnfZero :: ihqRowAdd (ihqZeroRow widthPred) frontPart)
      (qnfAdd headScalar qnfZero :: ihqRowAdd (ihqZeroRow widthPred) backPart)
    = ihqCat (headScalar :: frontPart) (headScalar :: backPart)
  rw [qnfAddZeroRight headScalar, ihqRowAddZeroLeft frontPart widthPred hFrontLen,
    ihqRowAddZeroLeft backPart widthPred hBackLen]

/-- The identity spec: `ihqIdRows` denotes exactly the diagonal relation (the
QnfRat port of the F2 template's `zxpIdSpec`; the F2 head-bit case split becomes
a single scalar-head telescope over the field). -/
theorem ihsIdSpec : (identityWidth : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem identityWidth identityWidth (ihqIdRows identityWidth) domVec codVec
      <-> (domVec = codVec /\ domVec.length = identityWidth))
  | 0, domVec, codVec => by
      refine Iff.intro ?_ ?_
      · intro hPair
        have hDomNil := ihsLengthZeroNil domVec hPair.left
        have hCodNil := ihsLengthZeroNil codVec hPair.right.left
        rw [hDomNil, hCodNil]
        exact And.intro rfl rfl
      · intro hSame
        have hDomNil := ihsLengthZeroNil domVec hSame.right
        rw [<- hSame.left, hDomNil]
        exact And.intro rfl (And.intro rfl IhqMemSpan.zero)
  | widthPred + 1, domVec, codVec => by
      have hIdAllPred := ihqIdRowsWidth widthPred
      refine Iff.intro ?_ ?_
      · intro hPair
        have hDomLen : domVec.length = widthPred + 1 := hPair.left
        have hSplit := ihqMemSpanConsInv hPair.right.right
        cases hSplit with
        | inl hInMapped =>
            have hMapInv := ihqMapRowsSpanFwd (ihqPadPairRow widthPred)
              (ihsPadPairRowZero widthPred)
              (fun firstPair secondPair hFirstLen hSecondLen =>
                ihsPadPairRowAdd widthPred firstPair secondPair hFirstLen hSecondLen)
              (fun scalar rowPair _hRowLen =>
                ihsPadPairRowScale widthPred scalar rowPair)
              hIdAllPred hInMapped
            cases hMapInv with
            | intro innerPair hBoth =>
                have hInnerLen : innerPair.length = widthPred + widthPred :=
                  ihqMemSpanWidth hIdAllPred hBoth.left
                have hPadShape : ihqPadPairRow widthPred innerPair
                    = ihqCat (qnfZero :: ihqTakeN widthPred innerPair)
                        (qnfZero :: ihqDropN widthPred innerPair) := rfl
                rw [hPadShape] at hBoth
                have hOuterSplit := ihqCatInj domVec codVec
                  (qnfZero :: ihqTakeN widthPred innerPair)
                  (qnfZero :: ihqDropN widthPred innerPair)
                  (by
                    show domVec.length = (ihqTakeN widthPred innerPair).length + 1
                    rw [hDomLen, ihqTakeNLength innerPair widthPred widthPred hInnerLen])
                  hBoth.right
                have hInnerPairMem : IhqPairMem widthPred widthPred
                    (ihqIdRows widthPred) (ihqTakeN widthPred innerPair)
                    (ihqDropN widthPred innerPair) := by
                  refine And.intro
                    (ihqTakeNLength innerPair widthPred widthPred hInnerLen)
                    (And.intro (ihqDropNLength innerPair widthPred widthPred hInnerLen)
                      ?_)
                  rw [ihqCatTakeDrop innerPair widthPred widthPred hInnerLen]
                  exact hBoth.left
                have hInnerSame := (ihsIdSpec widthPred (ihqTakeN widthPred innerPair)
                  (ihqDropN widthPred innerPair)).mp hInnerPairMem
                refine And.intro ?_ hDomLen
                rw [hOuterSplit.left, hOuterSplit.right, hInnerSame.left]
        | inr hSplitPack =>
            cases hSplitPack with
            | intro headScalar hPartnerPack =>
                cases hPartnerPack with
                | intro partner hBoth =>
                    have hMapInv := ihqMapRowsSpanFwd (ihqPadPairRow widthPred)
                      (ihsPadPairRowZero widthPred)
                      (fun firstPair secondPair hFirstLen hSecondLen =>
                        ihsPadPairRowAdd widthPred firstPair secondPair hFirstLen
                          hSecondLen)
                      (fun scalar rowPair _hRowLen =>
                        ihsPadPairRowScale widthPred scalar rowPair)
                      hIdAllPred hBoth.left
                    cases hMapInv with
                    | intro innerPair hInnerBoth =>
                        have hInnerLen : innerPair.length = widthPred + widthPred :=
                          ihqMemSpanWidth hIdAllPred hInnerBoth.left
                        have hVecShape : ihqCat domVec codVec
                            = ihqCat (headScalar :: ihqTakeN widthPred innerPair)
                                (headScalar :: ihqDropN widthPred innerPair) := by
                          rw [hBoth.right, hInnerBoth.right]
                          exact ihsIdHeadCombine widthPred headScalar
                            (ihqTakeN widthPred innerPair)
                            (ihqDropN widthPred innerPair)
                            (ihqTakeNLength innerPair widthPred widthPred hInnerLen)
                            (ihqDropNLength innerPair widthPred widthPred hInnerLen)
                        have hOuterSplit := ihqCatInj domVec codVec
                          (headScalar :: ihqTakeN widthPred innerPair)
                          (headScalar :: ihqDropN widthPred innerPair)
                          (by
                            show domVec.length
                              = (ihqTakeN widthPred innerPair).length + 1
                            rw [hDomLen,
                              ihqTakeNLength innerPair widthPred widthPred hInnerLen])
                          hVecShape
                        have hInnerPairMem : IhqPairMem widthPred widthPred
                            (ihqIdRows widthPred) (ihqTakeN widthPred innerPair)
                            (ihqDropN widthPred innerPair) := by
                          refine And.intro
                            (ihqTakeNLength innerPair widthPred widthPred hInnerLen)
                            (And.intro
                              (ihqDropNLength innerPair widthPred widthPred hInnerLen)
                              ?_)
                          rw [ihqCatTakeDrop innerPair widthPred widthPred hInnerLen]
                          exact hInnerBoth.left
                        have hInnerSame :=
                          (ihsIdSpec widthPred (ihqTakeN widthPred innerPair)
                            (ihqDropN widthPred innerPair)).mp hInnerPairMem
                        refine And.intro ?_ hDomLen
                        rw [hOuterSplit.left, hOuterSplit.right, hInnerSame.left]
      · intro hSame
        cases hSame with
        | intro hEqVecs hDomLen =>
            rw [<- hEqVecs]
            cases domVec with
            | nil => exact nomatch hDomLen
            | cons headCoeff restVec =>
                have hRestLen : restVec.length = widthPred := Nat.succ.inj hDomLen
                have hInnerPairMem := (ihsIdSpec widthPred restVec restVec).mpr
                  (And.intro rfl hRestLen)
                have hMapped := ihqMapRowsSpanBwd (ihqPadPairRow widthPred)
                  (ihsPadPairRowZero widthPred)
                  (fun firstPair secondPair hFirstLen hSecondLen =>
                    ihsPadPairRowAdd widthPred firstPair secondPair hFirstLen
                      hSecondLen)
                  (fun scalar rowPair _hRowLen =>
                    ihsPadPairRowScale widthPred scalar rowPair)
                  hIdAllPred hInnerPairMem.right.right
                have hPadEq : ihqPadPairRow widthPred (ihqCat restVec restVec)
                    = ihqCat (qnfZero :: restVec) (qnfZero :: restVec) := by
                  show ihqCat
                      (qnfZero :: ihqTakeN widthPred (ihqCat restVec restVec))
                      (qnfZero :: ihqDropN widthPred (ihqCat restVec restVec))
                    = ihqCat (qnfZero :: restVec) (qnfZero :: restVec)
                  rw [ihqTakeNCatExact restVec restVec widthPred hRestLen,
                    ihqDropNCatExact restVec restVec widthPred hRestLen]
                rw [hPadEq] at hMapped
                have hWeakened := ihqMemSpanWeaken
                  (ihqCat (qnfOne :: ihqZeroRow widthPred)
                    (qnfOne :: ihqZeroRow widthPred))
                  hMapped
                have hPicked := IhqMemSpan.pick headCoeff
                  (ihqCat (qnfOne :: ihqZeroRow widthPred)
                    (qnfOne :: ihqZeroRow widthPred))
                  (IhqRowMem.head _ _) hWeakened
                have hCombine := ihsIdHeadCombine widthPred headCoeff restVec restVec
                  hRestLen hRestLen
                rw [hCombine] at hPicked
                exact And.intro hDomLen (And.intro hDomLen hPicked)

/-! ## Stage 6 — the categorical laws the sequential congruence needs -/

/-- Composition respects relation equivalence on both sides. -/
theorem ihsComposeRowsCong (domWidth midWidth codWidth : Nat)
    {firstRows firstRows2 secondRows secondRows2 : List (List QnfRat)}
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hFirstAll2 : IhqAllWidth (domWidth + midWidth) firstRows2)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows)
    (hSecondAll2 : IhqAllWidth (midWidth + codWidth) secondRows2)
    (hLeft : IhsRelEquiv domWidth midWidth firstRows firstRows2)
    (hRight : IhsRelEquiv midWidth codWidth secondRows secondRows2) :
    IhsRelEquiv domWidth codWidth
      (ihqComposeRows domWidth midWidth codWidth firstRows secondRows)
      (ihqComposeRows domWidth midWidth codWidth firstRows2 secondRows2) := by
  intro domVec codVec
  refine Iff.trans (ihqComposeSpec domWidth midWidth codWidth firstRows secondRows
    hFirstAll hSecondAll domVec codVec)
    (Iff.trans ?_ (ihqComposeSpec domWidth midWidth codWidth firstRows2 secondRows2
      hFirstAll2 hSecondAll2 domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBothParts =>
        exact Exists.intro midVec
          (And.intro ((hLeft domVec midVec).mp hBothParts.left)
            ((hRight midVec codVec).mp hBothParts.right))
  · intro hExists
    cases hExists with
    | intro midVec hBothParts =>
        exact Exists.intro midVec
          (And.intro ((hLeft domVec midVec).mpr hBothParts.left)
            ((hRight midVec codVec).mpr hBothParts.right))

/-- Composition is associative up to relation equivalence. -/
theorem ihsComposeRowsAssoc (domWidth midWidth secondMidWidth codWidth : Nat)
    (firstRows secondRows thirdRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + secondMidWidth) secondRows)
    (hThirdAll : IhqAllWidth (secondMidWidth + codWidth) thirdRows) :
    IhsRelEquiv domWidth codWidth
      (ihqComposeRows domWidth secondMidWidth codWidth
        (ihqComposeRows domWidth midWidth secondMidWidth firstRows secondRows)
        thirdRows)
      (ihqComposeRows domWidth midWidth codWidth firstRows
        (ihqComposeRows midWidth secondMidWidth codWidth secondRows thirdRows)) := by
  have hInnerLeftAll := ihqComposeRowsWidth domWidth midWidth secondMidWidth
    firstRows secondRows hFirstAll hSecondAll
  have hInnerRightAll := ihqComposeRowsWidth midWidth secondMidWidth codWidth
    secondRows thirdRows hSecondAll hThirdAll
  intro domVec codVec
  refine Iff.trans (ihqComposeSpec domWidth secondMidWidth codWidth _ thirdRows
    hInnerLeftAll hThirdAll domVec codVec)
    (Iff.trans ?_ (ihqComposeSpec domWidth midWidth codWidth firstRows _
      hFirstAll hInnerRightAll domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro secondMidVec hBothParts =>
        have hInner := (ihqComposeSpec domWidth midWidth secondMidWidth firstRows
          secondRows hFirstAll hSecondAll domVec secondMidVec).mp hBothParts.left
        cases hInner with
        | intro midVec hInnerBoth =>
            refine Exists.intro midVec (And.intro hInnerBoth.left ?_)
            refine (ihqComposeSpec midWidth secondMidWidth codWidth secondRows
              thirdRows hSecondAll hThirdAll midVec codVec).mpr ?_
            exact Exists.intro secondMidVec
              (And.intro hInnerBoth.right hBothParts.right)
  · intro hExists
    cases hExists with
    | intro midVec hBothParts =>
        have hInner := (ihqComposeSpec midWidth secondMidWidth codWidth secondRows
          thirdRows hSecondAll hThirdAll midVec codVec).mp hBothParts.right
        cases hInner with
        | intro secondMidVec hInnerBoth =>
            refine Exists.intro secondMidVec (And.intro ?_ hInnerBoth.right)
            refine (ihqComposeSpec domWidth midWidth secondMidWidth firstRows
              secondRows hFirstAll hSecondAll domVec secondMidVec).mpr ?_
            exact Exists.intro midVec (And.intro hBothParts.left hInnerBoth.left)

/-- Left unit law. -/
theorem ihsComposeIdLeft (domWidth codWidth : Nat) (rows : List (List QnfRat))
    (hAll : IhqAllWidth (domWidth + codWidth) rows) :
    IhsRelEquiv domWidth codWidth
      (ihqComposeRows domWidth domWidth codWidth (ihqIdRows domWidth) rows) rows := by
  intro domVec codVec
  refine Iff.trans (ihqComposeSpec domWidth domWidth codWidth (ihqIdRows domWidth)
    rows (ihqIdRowsWidth domWidth) hAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBothParts =>
        have hSame := (ihsIdSpec domWidth domVec midVec).mp hBothParts.left
        rw [hSame.left]
        exact hBothParts.right
  · intro hPair
    refine Exists.intro domVec (And.intro ?_ hPair)
    exact (ihsIdSpec domWidth domVec domVec).mpr (And.intro rfl hPair.left)

/-- Right unit law. -/
theorem ihsComposeIdRight (domWidth codWidth : Nat) (rows : List (List QnfRat))
    (hAll : IhqAllWidth (domWidth + codWidth) rows) :
    IhsRelEquiv domWidth codWidth
      (ihqComposeRows domWidth codWidth codWidth rows (ihqIdRows codWidth)) rows := by
  intro domVec codVec
  refine Iff.trans (ihqComposeSpec domWidth codWidth codWidth rows
    (ihqIdRows codWidth) hAll (ihqIdRowsWidth codWidth) domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBothParts =>
        have hSame := (ihsIdSpec codWidth midVec codVec).mp hBothParts.right
        rw [<- hSame.left]
        exact hBothParts.left
  · intro hPair
    refine Exists.intro codVec (And.intro hPair ?_)
    exact (ihsIdSpec codWidth codVec codVec).mpr (And.intro rfl hPair.right.left)

/-! ## Stage 7 — snoc plumbing for the append-layer congruence -/

/-- Append one layer at the end of a layer list. -/
def ihsSnocLayers : List (List IhsCell) -> List IhsCell -> List (List IhsCell)
  | [], lastLayer => [lastLayer]
  | headLayer :: restLayers, lastLayer =>
      headLayer :: ihsSnocLayers restLayers lastLayer

/-- The cod arity of a snoc is the appended layer's cod arity. -/
theorem ihsLayersCodAritySnoc : (layers : List (List IhsCell)) ->
    (lastLayer : List IhsCell) -> (currentArity : Nat) ->
    ihsLayersCodArity currentArity (ihsSnocLayers layers lastLayer)
      = ihsLayerCodArity lastLayer
  | [], _lastLayer, _currentArity => rfl
  | headLayer :: restLayers, lastLayer, _currentArity =>
      ihsLayersCodAritySnoc restLayers lastLayer (ihsLayerCodArity headLayer)

theorem ihsLayersWFSnoc : (layers : List (List IhsCell)) ->
    (lastLayer : List IhsCell) -> {currentArity : Nat} ->
    IhsLayersWF currentArity layers ->
    ihsLayerDomArity lastLayer = ihsLayersCodArity currentArity layers ->
    IhsLayersWF currentArity (ihsSnocLayers layers lastLayer)
  | [], _lastLayer, currentArity, _hWF, hFit =>
      IhsLayersWF.cons hFit (IhsLayersWF.nil _)
  | _headLayer :: restLayers, lastLayer, _currentArity, hWF, hFit => by
      cases hWF with
      | cons hDom hRest =>
          exact IhsLayersWF.cons hDom
            (ihsLayersWFSnoc restLayers lastLayer hRest hFit)

/-- Denotation of a snoc: composing the prefix denotation with the appended
layer's denotation (the sequential-decomposition workhorse). -/
theorem ihsLayersDenoteSnoc : (layers : List (List IhsCell)) ->
    (lastLayer : List IhsCell) -> (currentArity : Nat) ->
    IhsLayersWF currentArity layers ->
    ihsLayerDomArity lastLayer = ihsLayersCodArity currentArity layers ->
    IhsRelEquiv currentArity (ihsLayerCodArity lastLayer)
      (ihsLayersDenote currentArity (ihsSnocLayers layers lastLayer))
      (ihqComposeRows currentArity (ihsLayersCodArity currentArity layers)
        (ihsLayerCodArity lastLayer)
        (ihsLayersDenote currentArity layers) (ihsLayerDenote lastLayer))
  | [], lastLayer, currentArity, _hWF, hFit => by
      have hLastAll : IhqAllWidth (currentArity + ihsLayerCodArity lastLayer)
          (ihsLayerDenote lastLayer) :=
        ihsAllWidthCast
          (congrArg (fun boundaryArity =>
            boundaryArity + ihsLayerCodArity lastLayer) hFit)
          (ihsLayerDenoteWidth lastLayer)
      exact ihsRelEquivTrans
        (ihsComposeIdRight currentArity (ihsLayerCodArity lastLayer)
          (ihsLayerDenote lastLayer) hLastAll)
        (ihsRelEquivSymm
          (ihsComposeIdLeft currentArity (ihsLayerCodArity lastLayer)
            (ihsLayerDenote lastLayer) hLastAll))
  | headLayer :: restLayers, lastLayer, currentArity, hWF, hFit => by
      cases hWF with
      | cons hDom hRest =>
          show IhsRelEquiv currentArity (ihsLayerCodArity lastLayer)
            (ihqComposeRows currentArity (ihsLayerCodArity headLayer)
              (ihsLayersCodArity (ihsLayerCodArity headLayer)
                (ihsSnocLayers restLayers lastLayer))
              (ihsLayerDenote headLayer)
              (ihsLayersDenote (ihsLayerCodArity headLayer)
                (ihsSnocLayers restLayers lastLayer)))
            _
          rw [ihsLayersCodAritySnoc restLayers lastLayer (ihsLayerCodArity headLayer)]
          have hHeadAll : IhqAllWidth (currentArity + ihsLayerCodArity headLayer)
              (ihsLayerDenote headLayer) :=
            ihsAllWidthCast
              (congrArg (fun boundaryArity =>
                boundaryArity + ihsLayerCodArity headLayer) hDom)
              (ihsLayerDenoteWidth headLayer)
          have hRestDenAll := ihsLayersDenoteWidth restLayers hRest
          have hLastAll : IhqAllWidth
              (ihsLayersCodArity (ihsLayerCodArity headLayer) restLayers
                + ihsLayerCodArity lastLayer)
              (ihsLayerDenote lastLayer) :=
            ihsAllWidthCast
              (congrArg (fun boundaryArity =>
                boundaryArity + ihsLayerCodArity lastLayer) hFit)
              (ihsLayerDenoteWidth lastLayer)
          have hSnocDenAll : IhqAllWidth
              (ihsLayerCodArity headLayer + ihsLayerCodArity lastLayer)
              (ihsLayersDenote (ihsLayerCodArity headLayer)
                (ihsSnocLayers restLayers lastLayer)) :=
            ihsAllWidthCast
              (congrArg (fun tailCod => ihsLayerCodArity headLayer + tailCod)
                (ihsLayersCodAritySnoc restLayers lastLayer
                  (ihsLayerCodArity headLayer)))
              (ihsLayersDenoteWidth (ihsSnocLayers restLayers lastLayer)
                (ihsLayersWFSnoc restLayers lastLayer hRest hFit))
          have hComposeRestLastAll := ihqComposeRowsWidth (ihsLayerCodArity headLayer)
            (ihsLayersCodArity (ihsLayerCodArity headLayer) restLayers)
            (ihsLayerCodArity lastLayer)
            (ihsLayersDenote (ihsLayerCodArity headLayer) restLayers)
            (ihsLayerDenote lastLayer) hRestDenAll hLastAll
          have hStepCong := ihsComposeRowsCong currentArity
            (ihsLayerCodArity headLayer) (ihsLayerCodArity lastLayer)
            hHeadAll hHeadAll hSnocDenAll hComposeRestLastAll
            (ihsRelEquivRefl currentArity (ihsLayerCodArity headLayer)
              (ihsLayerDenote headLayer))
            (ihsLayersDenoteSnoc restLayers lastLayer (ihsLayerCodArity headLayer)
              hRest hFit)
          have hStepAssoc := ihsRelEquivSymm
            (ihsComposeRowsAssoc currentArity (ihsLayerCodArity headLayer)
              (ihsLayersCodArity (ihsLayerCodArity headLayer) restLayers)
              (ihsLayerCodArity lastLayer)
              (ihsLayerDenote headLayer)
              (ihsLayersDenote (ihsLayerCodArity headLayer) restLayers)
              (ihsLayerDenote lastLayer) hHeadAll hRestDenAll hLastAll)
          exact ihsRelEquivTrans hStepCong hStepAssoc

/-! ## Stage 8 — the relation set (T3)

Every axiom family of BSZ Definition 6.1 as an (lhs, rhs) diagram pair, one
constructor per row.  Scalar-indexed families are instantiated at small
scalars (k = 2, k1 = 2 / k2 = 3, sum 5, product 6, antipode -1) — see the
honesty note on `ihsRowGateFires` and the general-scalar theorems
`ihsScalarZeroAbsorbGeneral` / `ihsScalarCozeroAbsorbGeneral`.  Each
constructor docstring cites its census tag verbatim; the full census lives on
`ihsCompletenessStatement`. -/

/-- The shipped IH_Q rewrite rows (46 = 18 A + 18 A-op + 10 I, counting each
Frobenius chain as two equations, per the census). -/
inductive IhsRowTag : Type where
  /-- A1 unit: `add(zero (x) id) = id` (1->1). -/
  | addUnit : IhsRowTag
  /-- A2 comm: `swap;add = add` (2->1). -/
  | addComm : IhsRowTag
  /-- A3 assoc: `(add (x) id);add = (id (x) add);add` (3->1). -/
  | addAssoc : IhsRowTag
  /-- A4 counit: `copy;(discard (x) id) = id` (1->1). -/
  | copyCounit : IhsRowTag
  /-- A5 cocomm: `copy;swap = copy` (1->2). -/
  | copyCocomm : IhsRowTag
  /-- A6 coassoc: `copy;(copy (x) id) = copy;(id (x) copy)` (1->3). -/
  | copyCoassoc : IhsRowTag
  /-- A7 mult-counit: `add;discard = discard (x) discard` (2->0). -/
  | addDiscard : IhsRowTag
  /-- A8 bimonoid: `add;copy = (copy (x) copy);(id (x) swap (x) id);(add (x) add)` (2->2). -/
  | bimonoid : IhsRowTag
  /-- A9 unit-comult: `zero;copy = zero (x) zero` (0->2). -/
  | zeroCopy : IhsRowTag
  /-- A10 unit-counit: `zero;discard = id_0` (0->0). -/
  | zeroDiscard : IhsRowTag
  /-- A11 one: `scalar 1 = id` (1->1). -/
  | scalarOne : IhsRowTag
  /-- A12 product: `k1;k2 = k1*k2` (1->1), instance k1 = 2, k2 = 3, product 6. -/
  | scalarProduct : IhsRowTag
  /-- A13 scalar/add: `add;k = (k (x) k);add` (2->1), instance k = 2. -/
  | scalarThroughAdd : IhsRowTag
  /-- A14 scalar/zero: `zero;k = zero` (0->1), instance k = 2 (general-scalar
  raw-compose form: `ihsScalarZeroAbsorbGeneral`). -/
  | scalarAfterZero : IhsRowTag
  /-- A15 scalar/copy: `k;copy = copy;(k (x) k)` (1->2), instance k = 2. -/
  | scalarThroughCopy : IhsRowTag
  /-- A16 scalar/discard: `k;discard = discard` (1->0), instance k = 2. -/
  | scalarIntoDiscard : IhsRowTag
  /-- A17 zero-scalar: `scalar 0 = discard;zero` (1->1). -/
  | scalarZeroBox : IhsRowTag
  /-- A18 sum: `copy;(k1 (x) k2);add = scalar (k1+k2)` (1->1), instance 2 + 3 = 5. -/
  | scalarSum : IhsRowTag
  /-- A1op unit-mirror: `coadd;(cozero (x) id) = id` (1->1). -/
  | coaddCounit : IhsRowTag
  /-- A2op comm-mirror: `coadd;swap = coadd` (1->2). -/
  | coaddCocomm : IhsRowTag
  /-- A3op assoc-mirror: `coadd;(coadd (x) id) = coadd;(id (x) coadd)` (1->3). -/
  | coaddCoassoc : IhsRowTag
  /-- A4op counit-mirror: `(blackunit (x) id);cocopy = id` (1->1). -/
  | cocopyUnit : IhsRowTag
  /-- A5op cocomm-mirror: `swap;cocopy = cocopy` (2->1). -/
  | cocopyComm : IhsRowTag
  /-- A6op coassoc-mirror: `(cocopy (x) id);cocopy = (id (x) cocopy);cocopy` (3->1). -/
  | cocopyAssoc : IhsRowTag
  /-- A7op mult-counit-mirror: `blackunit;coadd = blackunit (x) blackunit` (0->2). -/
  | unitCoadd : IhsRowTag
  /-- A8op bimonoid-mirror: `cocopy;coadd
  = (coadd (x) coadd);(id (x) swap (x) id);(cocopy (x) cocopy)` (2->2). -/
  | bimonoidOp : IhsRowTag
  /-- A9op unit-comult-mirror: `cocopy;cozero = cozero (x) cozero` (2->0). -/
  | cocopyCozero : IhsRowTag
  /-- A10op unit-counit-mirror: `blackunit;cozero = id_0` (0->0). -/
  | unitCozero : IhsRowTag
  /-- A11op one-mirror: `mirror-scalar 1 = id` (1->1). -/
  | scalarOneOp : IhsRowTag
  /-- A12op product-mirror: `k1-mirror;k2-mirror = (product)-mirror` (1->1),
  instance 2-mirror;3-mirror = 6-mirror. -/
  | scalarProductOp : IhsRowTag
  /-- A13op scalar/add-mirror: `k-mirror;coadd = coadd;(k-mirror (x) k-mirror)`
  (1->2), instance k = 2. -/
  | scalarThroughCoaddOp : IhsRowTag
  /-- A14op scalar/zero-mirror: `k-mirror;cozero = cozero` (1->0), instance k = 2
  (general-scalar raw-compose form: `ihsScalarCozeroAbsorbGeneral`). -/
  | scalarIntoCozeroOp : IhsRowTag
  /-- A15op scalar/copy-mirror: `cocopy;k-mirror = (k-mirror (x) k-mirror);cocopy`
  (2->1), instance k = 2. -/
  | scalarThroughCocopyOp : IhsRowTag
  /-- A16op scalar/discard-mirror: `blackunit;k-mirror = blackunit` (0->1),
  instance k = 2. -/
  | scalarAfterUnitOp : IhsRowTag
  /-- A17op zero-scalar-mirror: `0-mirror = cozero;blackunit` (1->1). -/
  | scalarZeroBoxOp : IhsRowTag
  /-- A18op sum-mirror: `coadd;(k1-mirror (x) k2-mirror);cocopy = (sum)-mirror`
  (1->1), instance 2 + 3 = 5. -/
  | scalarSumOp : IhsRowTag
  /-- I1 fwd-cancel [= (W1)]: `l;l-mirror = id` (1->1), l nonzero only,
  instance l = 2. -/
  | forwardCancel : IhsRowTag
  /-- I2 bwd-cancel [= (B1)]: `l-mirror;l = id` (1->1), l nonzero only,
  instance l = 2. -/
  | backwardCancel : IhsRowTag
  /-- I3 white Frobenius [= W3 = B4], left equation of the chain:
  `(coadd (x) id);(id (x) add) = add;coadd` (2->2). -/
  | whiteFrobeniusLeft : IhsRowTag
  /-- I3 white Frobenius [= W3 = B4], right equation of the chain:
  `(id (x) coadd);(add (x) id) = add;coadd` (2->2). -/
  | whiteFrobeniusRight : IhsRowTag
  /-- I4 black Frobenius [= W4 = B3], left equation of the chain:
  `(copy (x) id);(id (x) cocopy) = cocopy;copy` (2->2). -/
  | blackFrobeniusLeft : IhsRowTag
  /-- I4 black Frobenius [= W4 = B3], right equation of the chain:
  `(id (x) copy);(cocopy (x) id) = cocopy;copy` (2->2). -/
  | blackFrobeniusRight : IhsRowTag
  /-- I5 white/black cup [= W5]: `zero;coadd = blackunit;copy;(id (x) antipode)`
  (0->2); antipode = `scalarBox (-1)` on the lower (second) leg per the figure
  (leg choice interderivable via A5). -/
  | whiteBlackCup : IhsRowTag
  /-- I6 white/black cap [= W6]: `add;cozero = (antipode-mirror (x) id);cocopy;discard`
  (2->0); the figure draws the mirrored antipode `(-1)-mirror` on the upper
  (first) leg, transcribed faithfully (equal to `-1` only via derived law D3). -/
  | whiteBlackCap : IhsRowTag
  /-- I7 white special: `coadd;add = id` (1->1) (new in Def 6.1). -/
  | whiteSpecial : IhsRowTag
  /-- I8 black special: `copy;cocopy = id` (1->1) (new in Def 6.1; = derived (D11)
  in IH^Sp). -/
  | blackSpecial : IhsRowTag

/-- Left-hand side of each shipped row. -/
def ihsRowLhs : IhsRowTag -> IhsDiagram
  | IhsRowTag.addUnit =>
      { sourceArity := 1
        layers := [[IhsCell.whiteUnit, IhsCell.wire], [IhsCell.whiteMult]] }
  | IhsRowTag.addComm =>
      { sourceArity := 2, layers := [[IhsCell.crossing], [IhsCell.whiteMult]] }
  | IhsRowTag.addAssoc =>
      { sourceArity := 3
        layers := [[IhsCell.whiteMult, IhsCell.wire], [IhsCell.whiteMult]] }
  | IhsRowTag.copyCounit =>
      { sourceArity := 1
        layers := [[IhsCell.blackComult], [IhsCell.blackCounit, IhsCell.wire]] }
  | IhsRowTag.copyCocomm =>
      { sourceArity := 1, layers := [[IhsCell.blackComult], [IhsCell.crossing]] }
  | IhsRowTag.copyCoassoc =>
      { sourceArity := 1
        layers := [[IhsCell.blackComult], [IhsCell.blackComult, IhsCell.wire]] }
  | IhsRowTag.addDiscard =>
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.blackCounit]] }
  | IhsRowTag.bimonoid =>
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.blackComult]] }
  | IhsRowTag.zeroCopy =>
      { sourceArity := 0, layers := [[IhsCell.whiteUnit], [IhsCell.blackComult]] }
  | IhsRowTag.zeroDiscard =>
      { sourceArity := 0, layers := [[IhsCell.whiteUnit], [IhsCell.blackCounit]] }
  | IhsRowTag.scalarOne =>
      { sourceArity := 1, layers := [[IhsCell.scalarBox qnfOne]] }
  | IhsRowTag.scalarProduct =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo], [IhsCell.scalarBox ihsScalarThree]] }
  | IhsRowTag.scalarThroughAdd =>
      { sourceArity := 2
        layers := [[IhsCell.whiteMult], [IhsCell.scalarBox ihsScalarTwo]] }
  | IhsRowTag.scalarAfterZero =>
      { sourceArity := 0
        layers := [[IhsCell.whiteUnit], [IhsCell.scalarBox ihsScalarTwo]] }
  | IhsRowTag.scalarThroughCopy =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo], [IhsCell.blackComult]] }
  | IhsRowTag.scalarIntoDiscard =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo], [IhsCell.blackCounit]] }
  | IhsRowTag.scalarZeroBox =>
      { sourceArity := 1, layers := [[IhsCell.scalarBox qnfZero]] }
  | IhsRowTag.scalarSum =>
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox ihsScalarTwo, IhsCell.scalarBox ihsScalarThree],
          [IhsCell.whiteMult]] }
  | IhsRowTag.coaddCounit =>
      { sourceArity := 1
        layers := [[IhsCell.whiteComult], [IhsCell.whiteCounit, IhsCell.wire]] }
  | IhsRowTag.coaddCocomm =>
      { sourceArity := 1, layers := [[IhsCell.whiteComult], [IhsCell.crossing]] }
  | IhsRowTag.coaddCoassoc =>
      { sourceArity := 1
        layers := [[IhsCell.whiteComult], [IhsCell.whiteComult, IhsCell.wire]] }
  | IhsRowTag.cocopyUnit =>
      { sourceArity := 1
        layers := [[IhsCell.blackUnit, IhsCell.wire], [IhsCell.blackMult]] }
  | IhsRowTag.cocopyComm =>
      { sourceArity := 2, layers := [[IhsCell.crossing], [IhsCell.blackMult]] }
  | IhsRowTag.cocopyAssoc =>
      { sourceArity := 3
        layers := [[IhsCell.blackMult, IhsCell.wire], [IhsCell.blackMult]] }
  | IhsRowTag.unitCoadd =>
      { sourceArity := 0, layers := [[IhsCell.blackUnit], [IhsCell.whiteComult]] }
  | IhsRowTag.bimonoidOp =>
      { sourceArity := 2, layers := [[IhsCell.blackMult], [IhsCell.whiteComult]] }
  | IhsRowTag.cocopyCozero =>
      { sourceArity := 2, layers := [[IhsCell.blackMult], [IhsCell.whiteCounit]] }
  | IhsRowTag.unitCozero =>
      { sourceArity := 0, layers := [[IhsCell.blackUnit], [IhsCell.whiteCounit]] }
  | IhsRowTag.scalarOneOp =>
      { sourceArity := 1, layers := [[IhsCell.scalarBoxMirror qnfOne]] }
  | IhsRowTag.scalarProductOp =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo],
          [IhsCell.scalarBoxMirror ihsScalarThree]] }
  | IhsRowTag.scalarThroughCoaddOp =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo], [IhsCell.whiteComult]] }
  | IhsRowTag.scalarIntoCozeroOp =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo], [IhsCell.whiteCounit]] }
  | IhsRowTag.scalarThroughCocopyOp =>
      { sourceArity := 2
        layers := [[IhsCell.blackMult], [IhsCell.scalarBoxMirror ihsScalarTwo]] }
  | IhsRowTag.scalarAfterUnitOp =>
      { sourceArity := 0
        layers := [[IhsCell.blackUnit], [IhsCell.scalarBoxMirror ihsScalarTwo]] }
  | IhsRowTag.scalarZeroBoxOp =>
      { sourceArity := 1, layers := [[IhsCell.scalarBoxMirror qnfZero]] }
  | IhsRowTag.scalarSumOp =>
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror ihsScalarTwo, IhsCell.scalarBoxMirror ihsScalarThree],
          [IhsCell.blackMult]] }
  | IhsRowTag.forwardCancel =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.scalarBoxMirror ihsScalarTwo]] }
  | IhsRowTag.backwardCancel =>
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo],
          [IhsCell.scalarBox ihsScalarTwo]] }
  | IhsRowTag.whiteFrobeniusLeft =>
      { sourceArity := 2
        layers := [[IhsCell.whiteComult, IhsCell.wire],
          [IhsCell.wire, IhsCell.whiteMult]] }
  | IhsRowTag.whiteFrobeniusRight =>
      { sourceArity := 2
        layers := [[IhsCell.wire, IhsCell.whiteComult],
          [IhsCell.whiteMult, IhsCell.wire]] }
  | IhsRowTag.blackFrobeniusLeft =>
      { sourceArity := 2
        layers := [[IhsCell.blackComult, IhsCell.wire],
          [IhsCell.wire, IhsCell.blackMult]] }
  | IhsRowTag.blackFrobeniusRight =>
      { sourceArity := 2
        layers := [[IhsCell.wire, IhsCell.blackComult],
          [IhsCell.blackMult, IhsCell.wire]] }
  | IhsRowTag.whiteBlackCup =>
      { sourceArity := 0, layers := [[IhsCell.whiteUnit], [IhsCell.whiteComult]] }
  | IhsRowTag.whiteBlackCap =>
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.whiteCounit]] }
  | IhsRowTag.whiteSpecial =>
      { sourceArity := 1, layers := [[IhsCell.whiteComult], [IhsCell.whiteMult]] }
  | IhsRowTag.blackSpecial =>
      { sourceArity := 1, layers := [[IhsCell.blackComult], [IhsCell.blackMult]] }

/-- Right-hand side of each shipped row. -/
def ihsRowRhs : IhsRowTag -> IhsDiagram
  | IhsRowTag.addUnit => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.addComm => { sourceArity := 2, layers := [[IhsCell.whiteMult]] }
  | IhsRowTag.addAssoc =>
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.whiteMult], [IhsCell.whiteMult]] }
  | IhsRowTag.copyCounit => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.copyCocomm => { sourceArity := 1, layers := [[IhsCell.blackComult]] }
  | IhsRowTag.copyCoassoc =>
      { sourceArity := 1
        layers := [[IhsCell.blackComult], [IhsCell.wire, IhsCell.blackComult]] }
  | IhsRowTag.addDiscard =>
      { sourceArity := 2, layers := [[IhsCell.blackCounit, IhsCell.blackCounit]] }
  | IhsRowTag.bimonoid =>
      { sourceArity := 2
        layers := [[IhsCell.blackComult, IhsCell.blackComult],
          [IhsCell.wire, IhsCell.crossing, IhsCell.wire],
          [IhsCell.whiteMult, IhsCell.whiteMult]] }
  | IhsRowTag.zeroCopy =>
      { sourceArity := 0, layers := [[IhsCell.whiteUnit, IhsCell.whiteUnit]] }
  | IhsRowTag.zeroDiscard => { sourceArity := 0, layers := [] }
  | IhsRowTag.scalarOne => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.scalarProduct =>
      { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarSix]] }
  | IhsRowTag.scalarThroughAdd =>
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.whiteMult]] }
  | IhsRowTag.scalarAfterZero =>
      { sourceArity := 0, layers := [[IhsCell.whiteUnit]] }
  | IhsRowTag.scalarThroughCopy =>
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox ihsScalarTwo, IhsCell.scalarBox ihsScalarTwo]] }
  | IhsRowTag.scalarIntoDiscard =>
      { sourceArity := 1, layers := [[IhsCell.blackCounit]] }
  | IhsRowTag.scalarZeroBox =>
      { sourceArity := 1, layers := [[IhsCell.blackCounit], [IhsCell.whiteUnit]] }
  | IhsRowTag.scalarSum =>
      { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarFive]] }
  | IhsRowTag.coaddCounit => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.coaddCocomm => { sourceArity := 1, layers := [[IhsCell.whiteComult]] }
  | IhsRowTag.coaddCoassoc =>
      { sourceArity := 1
        layers := [[IhsCell.whiteComult], [IhsCell.wire, IhsCell.whiteComult]] }
  | IhsRowTag.cocopyUnit => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.cocopyComm => { sourceArity := 2, layers := [[IhsCell.blackMult]] }
  | IhsRowTag.cocopyAssoc =>
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.blackMult], [IhsCell.blackMult]] }
  | IhsRowTag.unitCoadd =>
      { sourceArity := 0, layers := [[IhsCell.blackUnit, IhsCell.blackUnit]] }
  | IhsRowTag.bimonoidOp =>
      { sourceArity := 2
        layers := [[IhsCell.whiteComult, IhsCell.whiteComult],
          [IhsCell.wire, IhsCell.crossing, IhsCell.wire],
          [IhsCell.blackMult, IhsCell.blackMult]] }
  | IhsRowTag.cocopyCozero =>
      { sourceArity := 2, layers := [[IhsCell.whiteCounit, IhsCell.whiteCounit]] }
  | IhsRowTag.unitCozero => { sourceArity := 0, layers := [] }
  | IhsRowTag.scalarOneOp => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.scalarProductOp =>
      { sourceArity := 1, layers := [[IhsCell.scalarBoxMirror ihsScalarSix]] }
  | IhsRowTag.scalarThroughCoaddOp =>
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror ihsScalarTwo, IhsCell.scalarBoxMirror ihsScalarTwo]] }
  | IhsRowTag.scalarIntoCozeroOp =>
      { sourceArity := 1, layers := [[IhsCell.whiteCounit]] }
  | IhsRowTag.scalarThroughCocopyOp =>
      { sourceArity := 2
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo,
          IhsCell.scalarBoxMirror ihsScalarTwo], [IhsCell.blackMult]] }
  | IhsRowTag.scalarAfterUnitOp =>
      { sourceArity := 0, layers := [[IhsCell.blackUnit]] }
  | IhsRowTag.scalarZeroBoxOp =>
      { sourceArity := 1, layers := [[IhsCell.whiteCounit], [IhsCell.blackUnit]] }
  | IhsRowTag.scalarSumOp =>
      { sourceArity := 1, layers := [[IhsCell.scalarBoxMirror ihsScalarFive]] }
  | IhsRowTag.forwardCancel => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.backwardCancel => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.whiteFrobeniusLeft =>
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.whiteComult]] }
  | IhsRowTag.whiteFrobeniusRight =>
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.whiteComult]] }
  | IhsRowTag.blackFrobeniusLeft =>
      { sourceArity := 2, layers := [[IhsCell.blackMult], [IhsCell.blackComult]] }
  | IhsRowTag.blackFrobeniusRight =>
      { sourceArity := 2, layers := [[IhsCell.blackMult], [IhsCell.blackComult]] }
  | IhsRowTag.whiteBlackCup =>
      { sourceArity := 0
        layers := [[IhsCell.blackUnit], [IhsCell.blackComult],
          [IhsCell.wire, IhsCell.scalarBox ihsAntipodeScalar]] }
  | IhsRowTag.whiteBlackCap =>
      { sourceArity := 2
        layers := [[IhsCell.scalarBoxMirror ihsAntipodeScalar, IhsCell.wire],
          [IhsCell.blackMult], [IhsCell.blackCounit]] }
  | IhsRowTag.whiteSpecial => { sourceArity := 1, layers := [[IhsCell.wire]] }
  | IhsRowTag.blackSpecial => { sourceArity := 1, layers := [[IhsCell.wire]] }

/-! ### The gate: every row passes the executable well-formedness + boundary +
relation-diff span decision, kernel-`rfl` -/

/-- One Bool bundling every executable check for one row: both sides pass the
well-formedness gate, boundaries agree, and the span decision fires. -/
def ihsRowGateB (tag : IhsRowTag) : Bool :=
  ihsAndB (ihsDiagramWFB (ihsRowLhs tag))
    (ihsAndB (ihsDiagramWFB (ihsRowRhs tag))
      (ihsAndB (ihsNatEqB (ihsRowLhs tag).sourceArity (ihsRowRhs tag).sourceArity)
        (ihsAndB (ihsNatEqB (ihsDiagramCodArity (ihsRowLhs tag))
            (ihsDiagramCodArity (ihsRowRhs tag)))
          (ihqSpanEqB (ihsDiagramDenote (ihsRowLhs tag))
            (ihsDiagramDenote (ihsRowRhs tag))))))

set_option maxHeartbeats 4000000 in
/-- The gate fires: for every shipped row, the whole executable check bundle
(well-formedness x2, boundary agreement x2, and the
`ihqSpanEqB (ihsDiagramDenote lhs) (ihsDiagramDenote rhs) = true` relation-diff
decision) is kernel-`rfl`.  On scalars: the scalar-indexed families (A11-A18,
their mirrors, I1/I2) are pinned at the small-scalar instances named in the row
docstrings (k = 2, k1 = 2/k2 = 3, antipode -1); the general-scalar rows are not
provable by `rfl` at the diagram level because `ihsLayersDenote` post-composes
with the identity relation and the echelonization then scrutinizes the symbolic
scalar.  The two families whose raw-compose forms are symbolic-scalar-`rfl` are
shipped in full generality as `ihsScalarZeroAbsorbGeneral` /
`ihsScalarCozeroAbsorbGeneral`. -/
theorem ihsRowGateFires : (tag : IhsRowTag) -> ihsRowGateB tag = true
  | IhsRowTag.addUnit => rfl
  | IhsRowTag.addComm => rfl
  | IhsRowTag.addAssoc => rfl
  | IhsRowTag.copyCounit => rfl
  | IhsRowTag.copyCocomm => rfl
  | IhsRowTag.copyCoassoc => rfl
  | IhsRowTag.addDiscard => rfl
  | IhsRowTag.bimonoid => rfl
  | IhsRowTag.zeroCopy => rfl
  | IhsRowTag.zeroDiscard => rfl
  | IhsRowTag.scalarOne => rfl
  | IhsRowTag.scalarProduct => rfl
  | IhsRowTag.scalarThroughAdd => rfl
  | IhsRowTag.scalarAfterZero => rfl
  | IhsRowTag.scalarThroughCopy => rfl
  | IhsRowTag.scalarIntoDiscard => rfl
  | IhsRowTag.scalarZeroBox => rfl
  | IhsRowTag.scalarSum => rfl
  | IhsRowTag.coaddCounit => rfl
  | IhsRowTag.coaddCocomm => rfl
  | IhsRowTag.coaddCoassoc => rfl
  | IhsRowTag.cocopyUnit => rfl
  | IhsRowTag.cocopyComm => rfl
  | IhsRowTag.cocopyAssoc => rfl
  | IhsRowTag.unitCoadd => rfl
  | IhsRowTag.bimonoidOp => rfl
  | IhsRowTag.cocopyCozero => rfl
  | IhsRowTag.unitCozero => rfl
  | IhsRowTag.scalarOneOp => rfl
  | IhsRowTag.scalarProductOp => rfl
  | IhsRowTag.scalarThroughCoaddOp => rfl
  | IhsRowTag.scalarIntoCozeroOp => rfl
  | IhsRowTag.scalarThroughCocopyOp => rfl
  | IhsRowTag.scalarAfterUnitOp => rfl
  | IhsRowTag.scalarZeroBoxOp => rfl
  | IhsRowTag.forwardCancel => rfl
  | IhsRowTag.backwardCancel => rfl
  | IhsRowTag.scalarSumOp => rfl
  | IhsRowTag.whiteFrobeniusLeft => rfl
  | IhsRowTag.whiteFrobeniusRight => rfl
  | IhsRowTag.blackFrobeniusLeft => rfl
  | IhsRowTag.blackFrobeniusRight => rfl
  | IhsRowTag.whiteBlackCup => rfl
  | IhsRowTag.whiteBlackCap => rfl
  | IhsRowTag.whiteSpecial => rfl
  | IhsRowTag.blackSpecial => rfl

/-- The span component of the gate, extracted: the T3 relation-diff pin per row. -/
theorem ihsRowSpanGate (tag : IhsRowTag) :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs tag))
      (ihsDiagramDenote (ihsRowRhs tag)) = true :=
  ihsAndBTrueRight _ _ (ihsAndBTrueRight _ _ (ihsAndBTrueRight _ _
    (ihsAndBTrueRight _ _ (ihsRowGateFires tag))))

/-! ### General-scalar theorems (the two symbolically-provable families) -/

/-- A14 (`zero ; k = zero`) for every scalar, at the raw relational-composition
level: the composite of the zero relation with the graph of any scalar is the
zero relation, literally (`rfl` with the scalar symbolic — the embedded row's
head is the closed `-1`, so echelonization never scrutinizes the scalar). -/
theorem ihsScalarZeroAbsorbGeneral (scalarValue : QnfRat) :
    ihqComposeRows 0 1 1 [] [[qnfOne, scalarValue]] = [] := rfl

/-- A14op (`k-mirror ; cozero = cozero`) for every scalar, at the raw
relational-composition level (`rfl` with the scalar symbolic — the embedded
row's head is the closed `1`). -/
theorem ihsScalarCozeroAbsorbGeneral (scalarValue : QnfRat) :
    ihqComposeRows 1 1 0 [[scalarValue, qnfOne]] [] = [] := rfl

/-! ## Stage 9 — the convertibility bundle, the congruence, soundness (T4) -/

/-- Everything soundness delivers for one convertibility edge. -/
def IhsConvBundle (firstDiagram secondDiagram : IhsDiagram) : Prop :=
  firstDiagram.sourceArity = secondDiagram.sourceArity
    /\ ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram
    /\ IhsDiagramWF firstDiagram /\ IhsDiagramWF secondDiagram
    /\ IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
        (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)

theorem ihsConvBundleSymm {firstDiagram secondDiagram : IhsDiagram}
    (hBundle : IhsConvBundle firstDiagram secondDiagram) :
    IhsConvBundle secondDiagram firstDiagram :=
  And.intro hBundle.left.symm
    (And.intro hBundle.right.left.symm
      (And.intro hBundle.right.right.right.left
        (And.intro hBundle.right.right.left
          (ihsRelEquivCast hBundle.left hBundle.right.left
            (ihsRelEquivSymm hBundle.right.right.right.right)))))

theorem ihsConvBundleTrans {firstDiagram secondDiagram thirdDiagram : IhsDiagram}
    (hFirst : IhsConvBundle firstDiagram secondDiagram)
    (hSecond : IhsConvBundle secondDiagram thirdDiagram) :
    IhsConvBundle firstDiagram thirdDiagram :=
  And.intro (hFirst.left.trans hSecond.left)
    (And.intro (hFirst.right.left.trans hSecond.right.left)
      (And.intro hFirst.right.right.left
        (And.intro hSecond.right.right.right.left
          (ihsRelEquivTrans hFirst.right.right.right.right
            (ihsRelEquivCast hFirst.left.symm hFirst.right.left.symm
              hSecond.right.right.right.right)))))

/-- Kernel-checkable bundle introduction: two executable well-formedness passes,
two boundary equalities, one span-decision pass. -/
theorem ihsConvBundleOfChecks (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWFB : ihsDiagramWFB firstDiagram = true)
    (hSecondWFB : ihsDiagramWFB secondDiagram = true)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram)
    (hSpan : ihqSpanEqB (ihsDiagramDenote firstDiagram)
      (ihsDiagramDenote secondDiagram) = true) :
    IhsConvBundle firstDiagram secondDiagram :=
  And.intro hSourceEq
    (And.intro hCodEq
      (And.intro (ihsDiagramWFOfB firstDiagram hFirstWFB)
        (And.intro (ihsDiagramWFOfB secondDiagram hSecondWFB)
          (ihsRelEquivOfSpanEqB
            (ihsDiagramDenoteWidth firstDiagram
              (ihsDiagramWFOfB firstDiagram hFirstWFB))
            (ihsAllWidthCast
              (Eq.trans
                (congrArg (fun boundaryArity =>
                  boundaryArity + ihsDiagramCodArity secondDiagram) hSourceEq.symm)
                (congrArg (fun boundaryArity =>
                  firstDiagram.sourceArity + boundaryArity) hCodEq.symm))
              (ihsDiagramDenoteWidth secondDiagram
                (ihsDiagramWFOfB secondDiagram hSecondWFB)))
            hSpan))))

/-- Soundness of every shipped row (bundle form), from the gate. -/
theorem ihsRowBundle (tag : IhsRowTag) :
    IhsConvBundle (ihsRowLhs tag) (ihsRowRhs tag) :=
  ihsConvBundleOfChecks (ihsRowLhs tag) (ihsRowRhs tag)
    (ihsAndBTrueLeft _ _ (ihsRowGateFires tag))
    (ihsAndBTrueLeft _ _ (ihsAndBTrueRight _ _ (ihsRowGateFires tag)))
    (ihsNatEqBSound _ _ (ihsAndBTrueLeft _ _ (ihsAndBTrueRight _ _
      (ihsAndBTrueRight _ _ (ihsRowGateFires tag)))))
    (ihsNatEqBSound _ _ (ihsAndBTrueLeft _ _ (ihsAndBTrueRight _ _
      (ihsAndBTrueRight _ _ (ihsAndBTrueRight _ _ (ihsRowGateFires tag))))))
    (ihsRowSpanGate tag)

/-- The sequential-scope congruence: the equivalence generated by the 46 rows
under reflexivity on well-formed diagrams, symmetry, transitivity, and layer
congruence on both sequential sides (prepend a fitting layer / append a fitting
layer). -/
inductive IhsConv : IhsDiagram -> IhsDiagram -> Prop where
  | row (tag : IhsRowTag) : IhsConv (ihsRowLhs tag) (ihsRowRhs tag)
  | reflWF (diagram : IhsDiagram) (hWF : IhsDiagramWF diagram) :
      IhsConv diagram diagram
  | symm {firstDiagram secondDiagram : IhsDiagram}
      (hConv : IhsConv firstDiagram secondDiagram) :
      IhsConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : IhsDiagram}
      (hFirst : IhsConv firstDiagram secondDiagram)
      (hSecond : IhsConv secondDiagram thirdDiagram) :
      IhsConv firstDiagram thirdDiagram
  | prependLayer (newLayer : List IhsCell) {firstDiagram secondDiagram : IhsDiagram}
      (hFit : ihsLayerCodArity newLayer = firstDiagram.sourceArity)
      (hConv : IhsConv firstDiagram secondDiagram) :
      IhsConv
        { sourceArity := ihsLayerDomArity newLayer
          layers := newLayer :: firstDiagram.layers }
        { sourceArity := ihsLayerDomArity newLayer
          layers := newLayer :: secondDiagram.layers }
  | appendLayer (newLayer : List IhsCell) {firstDiagram secondDiagram : IhsDiagram}
      (hFit : ihsLayerDomArity newLayer = ihsDiagramCodArity firstDiagram)
      (hConv : IhsConv firstDiagram secondDiagram) :
      IhsConv
        { sourceArity := firstDiagram.sourceArity
          layers := ihsSnocLayers firstDiagram.layers newLayer }
        { sourceArity := secondDiagram.sourceArity
          layers := ihsSnocLayers secondDiagram.layers newLayer }

/-- Soundness of the congruence: convertible diagrams share boundaries, are
well-formed, and denote the same Q-linear relation. -/
theorem ihsConvSound {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhsConv firstDiagram secondDiagram) :
    IhsConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | row tag => exact ihsRowBundle tag
  | reflWF diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (ihsRelEquivRefl diagram.sourceArity (ihsDiagramCodArity diagram)
          (ihsDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact ihsConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact ihsConvBundleTrans firstBundle secondBundle
  | prependLayer newLayer hFit _hConv innerBundle =>
      rename_i innerFirst innerSecond
      have hFit2 : ihsLayerCodArity newLayer = innerSecond.sourceArity :=
        hFit.trans innerBundle.left
      have hTailWF1 : IhsLayersWF (ihsLayerCodArity newLayer) innerFirst.layers :=
        ihsLayersWFCast hFit.symm innerBundle.right.right.left
      have hTailWF2 : IhsLayersWF (ihsLayerCodArity newLayer) innerSecond.layers :=
        ihsLayersWFCast hFit2.symm innerBundle.right.right.right.left
      have hCodsEq : ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers
          = ihsLayersCodArity (ihsLayerCodArity newLayer) innerSecond.layers :=
        Eq.trans
          (Eq.trans
            (congrArg (fun boundaryArity =>
              ihsLayersCodArity boundaryArity innerFirst.layers) hFit)
            innerBundle.right.left)
          (congrArg (fun boundaryArity =>
            ihsLayersCodArity boundaryArity innerSecond.layers) hFit2).symm
      have hTail1All := ihsLayersDenoteWidth innerFirst.layers hTailWF1
      have hTail2All := ihsLayersDenoteWidth innerSecond.layers hTailWF2
      have hTail2AllCast : IhqAllWidth
          (ihsLayerCodArity newLayer
            + ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
          (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers) :=
        ihsAllWidthCast
          (congrArg (fun tailCod => ihsLayerCodArity newLayer + tailCod)
            hCodsEq.symm) hTail2All
      have hEquivTail : IhsRelEquiv (ihsLayerCodArity newLayer)
          (ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
          (ihsLayersDenote (ihsLayerCodArity newLayer) innerFirst.layers)
          (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers) := by
        rw [congrArg (fun boundaryArity =>
          ihsLayersDenote boundaryArity innerSecond.layers) hFit2]
        rw [hFit]
        exact innerBundle.right.right.right.right
      have hNewAll := ihsLayerDenoteWidth newLayer
      have hPrepCong := ihsComposeRowsCong (ihsLayerDomArity newLayer)
        (ihsLayerCodArity newLayer)
        (ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
        hNewAll hNewAll hTail1All hTail2AllCast
        (ihsRelEquivRefl (ihsLayerDomArity newLayer) (ihsLayerCodArity newLayer)
          (ihsLayerDenote newLayer))
        hEquivTail
      have hSecondComposeArgsEq : ihqComposeRows (ihsLayerDomArity newLayer)
          (ihsLayerCodArity newLayer)
          (ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
          (ihsLayerDenote newLayer)
          (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers)
          = ihqComposeRows (ihsLayerDomArity newLayer)
              (ihsLayerCodArity newLayer)
              (ihsLayersCodArity (ihsLayerCodArity newLayer) innerSecond.layers)
              (ihsLayerDenote newLayer)
              (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers) :=
        congrArg (fun codBoundary => ihqComposeRows (ihsLayerDomArity newLayer)
          (ihsLayerCodArity newLayer) codBoundary (ihsLayerDenote newLayer)
          (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers)) hCodsEq
      refine And.intro rfl (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · exact hCodsEq
      · exact IhsLayersWF.cons rfl hTailWF1
      · exact IhsLayersWF.cons rfl hTailWF2
      · show IhsRelEquiv (ihsLayerDomArity newLayer)
          (ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
          (ihqComposeRows (ihsLayerDomArity newLayer) (ihsLayerCodArity newLayer)
            (ihsLayersCodArity (ihsLayerCodArity newLayer) innerFirst.layers)
            (ihsLayerDenote newLayer)
            (ihsLayersDenote (ihsLayerCodArity newLayer) innerFirst.layers))
          (ihqComposeRows (ihsLayerDomArity newLayer) (ihsLayerCodArity newLayer)
            (ihsLayersCodArity (ihsLayerCodArity newLayer) innerSecond.layers)
            (ihsLayerDenote newLayer)
            (ihsLayersDenote (ihsLayerCodArity newLayer) innerSecond.layers))
        rw [<- hSecondComposeArgsEq]
        exact hPrepCong
  | appendLayer newLayer hFit _hConv innerBundle =>
      rename_i innerFirst innerSecond
      have hSrcEq : innerFirst.sourceArity = innerSecond.sourceArity :=
        innerBundle.left
      have hCodEq : ihsLayersCodArity innerFirst.sourceArity innerFirst.layers
          = ihsLayersCodArity innerSecond.sourceArity innerSecond.layers :=
        innerBundle.right.left
      have hWF1 : IhsLayersWF innerFirst.sourceArity innerFirst.layers :=
        innerBundle.right.right.left
      have hWF2 : IhsLayersWF innerSecond.sourceArity innerSecond.layers :=
        innerBundle.right.right.right.left
      have hFit2 : ihsLayerDomArity newLayer
          = ihsLayersCodArity innerSecond.sourceArity innerSecond.layers :=
        hFit.trans hCodEq
      have hSnocCodEq : ihsLayersCodArity innerFirst.sourceArity
          (ihsSnocLayers innerFirst.layers newLayer)
          = ihsLayersCodArity innerSecond.sourceArity
              (ihsSnocLayers innerSecond.layers newLayer) := by
        rw [ihsLayersCodAritySnoc innerFirst.layers newLayer innerFirst.sourceArity,
          ihsLayersCodAritySnoc innerSecond.layers newLayer innerSecond.sourceArity]
      have hStepFirst := ihsLayersDenoteSnoc innerFirst.layers newLayer
        innerFirst.sourceArity hWF1 hFit
      have hStepSecond := ihsLayersDenoteSnoc innerSecond.layers newLayer
        innerSecond.sourceArity hWF2 hFit2
      have hDen1All := ihsLayersDenoteWidth innerFirst.layers hWF1
      have hDen2AllCast : IhqAllWidth
          (innerFirst.sourceArity
            + ihsLayersCodArity innerFirst.sourceArity innerFirst.layers)
          (ihsLayersDenote innerSecond.sourceArity innerSecond.layers) :=
        ihsAllWidthCast
          (Eq.trans
            (congrArg (fun boundaryArity => boundaryArity
              + ihsLayersCodArity innerSecond.sourceArity innerSecond.layers)
              hSrcEq.symm)
            (congrArg (fun tailCod => innerFirst.sourceArity + tailCod)
              hCodEq.symm))
          (ihsLayersDenoteWidth innerSecond.layers hWF2)
      have hNewAll : IhqAllWidth
          (ihsLayersCodArity innerFirst.sourceArity innerFirst.layers
            + ihsLayerCodArity newLayer)
          (ihsLayerDenote newLayer) :=
        ihsAllWidthCast
          (congrArg (fun boundaryArity =>
            boundaryArity + ihsLayerCodArity newLayer) hFit)
          (ihsLayerDenoteWidth newLayer)
      have hMidCong := ihsComposeRowsCong innerFirst.sourceArity
        (ihsLayersCodArity innerFirst.sourceArity innerFirst.layers)
        (ihsLayerCodArity newLayer)
        hDen1All hDen2AllCast hNewAll hNewAll
        innerBundle.right.right.right.right
        (ihsRelEquivRefl _ (ihsLayerCodArity newLayer) (ihsLayerDenote newLayer))
      have hMidArgsEq : ihqComposeRows innerFirst.sourceArity
          (ihsLayersCodArity innerFirst.sourceArity innerFirst.layers)
          (ihsLayerCodArity newLayer)
          (ihsLayersDenote innerSecond.sourceArity innerSecond.layers)
          (ihsLayerDenote newLayer)
          = ihqComposeRows innerSecond.sourceArity
              (ihsLayersCodArity innerSecond.sourceArity innerSecond.layers)
              (ihsLayerCodArity newLayer)
              (ihsLayersDenote innerSecond.sourceArity innerSecond.layers)
              (ihsLayerDenote newLayer) :=
        Eq.trans
          (congrArg (fun boundaryArity => ihqComposeRows boundaryArity
            (ihsLayersCodArity innerFirst.sourceArity innerFirst.layers)
            (ihsLayerCodArity newLayer)
            (ihsLayersDenote innerSecond.sourceArity innerSecond.layers)
            (ihsLayerDenote newLayer)) hSrcEq)
          (congrArg (fun midArity => ihqComposeRows innerSecond.sourceArity
            midArity (ihsLayerCodArity newLayer)
            (ihsLayersDenote innerSecond.sourceArity innerSecond.layers)
            (ihsLayerDenote newLayer)) hCodEq)
      have hStepSecondCast : IhsRelEquiv innerFirst.sourceArity
          (ihsLayerCodArity newLayer)
          (ihqComposeRows innerSecond.sourceArity
            (ihsLayersCodArity innerSecond.sourceArity innerSecond.layers)
            (ihsLayerCodArity newLayer)
            (ihsLayersDenote innerSecond.sourceArity innerSecond.layers)
            (ihsLayerDenote newLayer))
          (ihsLayersDenote innerSecond.sourceArity
            (ihsSnocLayers innerSecond.layers newLayer)) :=
        ihsRelEquivCast hSrcEq.symm rfl (ihsRelEquivSymm hStepSecond)
      refine And.intro hSrcEq (And.intro hSnocCodEq
        (And.intro (ihsLayersWFSnoc innerFirst.layers newLayer hWF1 hFit)
          (And.intro (ihsLayersWFSnoc innerSecond.layers newLayer hWF2 hFit2) ?_)))
      show IhsRelEquiv innerFirst.sourceArity
        (ihsLayersCodArity innerFirst.sourceArity
          (ihsSnocLayers innerFirst.layers newLayer))
        (ihsLayersDenote innerFirst.sourceArity
          (ihsSnocLayers innerFirst.layers newLayer))
        (ihsLayersDenote innerSecond.sourceArity
          (ihsSnocLayers innerSecond.layers newLayer))
      rw [ihsLayersCodAritySnoc innerFirst.layers newLayer innerFirst.sourceArity]
      refine ihsRelEquivTrans hStepFirst (ihsRelEquivTrans ?_ hStepSecondCast)
      rw [<- hMidArgsEq]
      exact hMidCong

/-- The refutation bridge: convertibility forces the executable span decision to
fire `true`; a kernel-computed `false` refutes convertibility outright. -/
theorem ihsConvSpanEqB {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhsConv firstDiagram secondDiagram) :
    ihqSpanEqB (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)
      = true := by
  have hBundle := ihsConvSound hConv
  exact ihsSpanEqBOfRelEquiv
    (ihsDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (ihsAllWidthCast
      (Eq.trans
        (congrArg (fun boundaryArity =>
          boundaryArity + ihsDiagramCodArity secondDiagram) hBundle.left.symm)
        (congrArg (fun boundaryArity =>
          firstDiagram.sourceArity + boundaryArity) hBundle.right.left.symm))
      (ihsDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-! ## Stage 10 — fires (T5) -/

/-- Fire (a true conv in sequential context): the black counit row (A4) fired
under a prepended scalar-2 layer, one row applied in context. -/
theorem ihsFireCounitRowInScalarContext :
    IhsConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo], [IhsCell.blackComult],
          [IhsCell.blackCounit, IhsCell.wire]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo], [IhsCell.wire]] } :=
  IhsConv.prependLayer [IhsCell.scalarBox ihsScalarTwo] rfl
    (IhsConv.row IhsRowTag.copyCounit)

/-- Fire (a true conv with an appended layer): the scalar-one row (A11) fired
under an appended scalar-3 layer. -/
theorem ihsFireScalarOneRowThenAppendedScalar :
    IhsConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox qnfOne], [IhsCell.scalarBox ihsScalarThree]] }
      { sourceArity := 1
        layers := [[IhsCell.wire], [IhsCell.scalarBox ihsScalarThree]] } :=
  IhsConv.appendLayer [IhsCell.scalarBox ihsScalarThree] rfl
    (IhsConv.row IhsRowTag.scalarOne)

/-- The white unit (zero) state as a diagram. -/
def ihsWhiteUnitDiagram : IhsDiagram :=
  { sourceArity := 0, layers := [[IhsCell.whiteUnit]] }

/-- The black unit (full-line) state as a diagram. -/
def ihsBlackUnitDiagram : IhsDiagram :=
  { sourceArity := 0, layers := [[IhsCell.blackUnit]] }

/-- False control: the white and black units denote different subspaces of Q^1
(the zero subspace vs the full line); the kernel decision fires `false`. -/
theorem ihsFireUnitsSpanDistinct :
    ihqSpanEqB (ihsDiagramDenote ihsWhiteUnitDiagram)
      (ihsDiagramDenote ihsBlackUnitDiagram) = false := rfl

/-- Negative direction: the white unit is not convertible to the black unit. -/
theorem ihsFireUnitsNotConv :
    Not (IhsConv ihsWhiteUnitDiagram ihsBlackUnitDiagram) :=
  fun hConv =>
    Bool.noConfusion ((ihsConvSpanEqB hConv).symm.trans ihsFireUnitsSpanDistinct)

/-- The scalar-2 box as a diagram. -/
def ihsScalarTwoDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarTwo]] }

/-- The scalar-3 box as a diagram. -/
def ihsScalarThreeDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarThree]] }

/-- False control: scalar 2 and scalar 3 denote different lines in Q^2, genuine
Q-content (over F2 there is one nonzero scalar; here the scalar family
separates). -/
theorem ihsFireScalarTwoThreeSpanDistinct :
    ihqSpanEqB (ihsDiagramDenote ihsScalarTwoDiagram)
      (ihsDiagramDenote ihsScalarThreeDiagram) = false := rfl

/-- Negative direction: scalar 2 is not convertible to scalar 3. -/
theorem ihsFireScalarTwoThreeNotConv :
    Not (IhsConv ihsScalarTwoDiagram ihsScalarThreeDiagram) :=
  fun hConv =>
    Bool.noConfusion
      ((ihsConvSpanEqB hConv).symm.trans ihsFireScalarTwoThreeSpanDistinct)

/-- The scalar-composition fire: `scalar 2 ; scalar 3` span-equals `scalar 6`,
kernel-decided on the diagram denotations (this is the A12 gate pin). -/
theorem ihsFireScalarCompositionSpan :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.scalarProduct))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.scalarProduct)) = true :=
  ihsRowSpanGate IhsRowTag.scalarProduct

/-- The scalar composition as a one-step derivation in the congruence. -/
theorem ihsFireScalarCompositionConv :
    IhsConv (ihsRowLhs IhsRowTag.scalarProduct) (ihsRowRhs IhsRowTag.scalarProduct) :=
  IhsConv.row IhsRowTag.scalarProduct

/-- Honesty pin: the executable well-formedness gate rejects a mis-plumbed
diagram (an `add` cell fed by a single wire). -/
theorem ihsFireIllFormedDetected :
    ihsDiagramWFB { sourceArity := 1, layers := [[IhsCell.whiteMult]] }
      = false := rfl

/-! ## Stage 11 — honesty markers and the owner-false completeness statement -/

/-- This seed ships the IH_Q diagram semantics and executable well-formedness
gate together with the 46-row relation gate decided by kernel `rfl`
(`ihsRowGateFires`) and the general-scalar absorb families, and proves the
sequential congruence `IhsConv` sound (`ihsConvSound`) with the refutation
bridge (`ihsConvSpanEqB` -> `Not IhsConv` on `false` pins). -/
def ihsHasSoundness : Bool := true

/-- Completeness statement (BSZ Theorem 6.4 direction: IH_Q = LinRel_Q, so
span-equal well-formed diagrams on matching boundaries should be convertible).

Not proven.  Two independent blockers, in order: (1) `IhsConv` is
sequential-only, so the statement as stated here is almost certainly false for
this congruence (a row cannot fire beside a parallel wire); the whisker
congruence must land first.  (2) A completeness push requires the
invariant-first gate (a normal-form census against the BSZ Section 6 pushout
normal form / Theorem 6.4 factorization) before any completeness induction.

Relation-diff table (transcribed from the literature; every shipped row is
tagged to it in its constructor docstring):

IH_Q relation census against BSZ "Interacting Hopf algebras"
(arXiv:1403.7048v4 = JPAA 2017; page/tag refs to v4) and Zanasi thesis
(arXiv:1805.03032; same tags, Def ~3.44/Thm 3.49/Rem 3.45).  IH_Q := IH_R at
R = Q (field => PID; frac(Q) = Q); Theorem 6.4: IH_Q iso SV_Q = LinRel_Q.
Definition 6.1 (p.32): IH_R = quotient of HA_R + HA_R^op by (I1)-(I8).
Notation: add = white mult, zero = white unit, copy = black comult,
discard = black counit (HA_Q side, Sect. 2-3); mirrors (HA_Q^op side, Sect. 3
p.10): coadd = white comult, cozero = white counit, cocopy = black mult,
blackunit = black unit; ";" = left-to-right composition.  LinRel_Q semantics:
add {((x,y),x+y)}, zero {((),0)}, copy {(x,(x,x))}, discard {(x,())},
k {(x,kx)}; mirror = relational converse.

1. Generator table (self-dual signature; Sect. 5 p.13 / Sect. 6 p.31 pushout):
   G1 add 2->1 | G2 zero 0->1 | G3 copy 1->2 | G4 discard 1->0
   G5 coadd 1->2 | G6 cozero 1->0 | G7 cocopy 2->1 | G8 blackunit 0->1
   G9 scalar k : 1->1 for every k in Q (including 0 and 1; A11/A17 make those
   definable but they are in the signature, Sect. 3 p.8)
   G10 mirror scalar k : 1->1 for every k (k-mirror = converse {(kx,x)})
   Not generators: antipode (:= scalar -1 box, Remark 3.4 p.9); cups/caps
   (defined circuits, Sect. 5.1 p.13-14); swap/id (PROP structure).

2. Relation table — 44 numbered families = 18 (A) + 18 (A-op) + 8 (I);
   counting each Frobenius chain as 2 equations: 46.
   A-block (HA_Q, Figs pp.5,7,8,9; k, k1, k2 range over all of Q):
   A1 unit: add(zero (x) id) = id (1->1) | A2 comm: swap;add = add (2->1)
   A3 assoc: (add (x) id);add = (id (x) add);add (3->1)
   A4 counit: copy;(discard (x) id) = id (1->1)
   A5 cocomm: copy;swap = copy (1->2)
   A6 coassoc: copy;(copy (x) id) = copy;(id (x) copy) (1->3)
   A7 mult-counit: add;discard = discard (x) discard (2->0)
   A8 bimonoid: add;copy = (copy (x) copy);(id (x) swap (x) id);(add (x) add) (2->2)
   A9 unit-comult: zero;copy = zero (x) zero (0->2)
   A10 unit-counit: zero;discard = empty diagram id_0 (0->0)
   A11 one: scalar 1 = id (1->1) | A12 product: k1;k2 = k1*k2 (1->1)
   A13 scalar/add: add;k = (k (x) k);add (2->1)
   A14 scalar/zero: zero;k = zero (0->1)
   A15 scalar/copy: k;copy = copy;(k (x) k) (1->2)
   A16 scalar/discard: k;discard = discard (1->0)
   A17 zero-scalar: scalar 0 = discard;zero (1->1)
   A18 sum: copy;(k1 (x) k2);add = scalar (k1+k2) (1->1)
   A1op-A18op: the same 18 "in the mirror" (Sect. 3 p.10) on G5-G8/G10, e.g.
   A13op: k-mirror;coadd = coadd;(k-mirror (x) k-mirror); A17op: 0-mirror =
   cozero;blackunit.
   I-block (Definition 6.1, p.32; l ranges over nonzero Q only, in I1-I2 only):
   I1 fwd-cancel: l;l-mirror = id (1->1), l /= 0 [= (W1), Def 5.1 p.13]
   I2 bwd-cancel: l-mirror;l = id (1->1), l /= 0 [= (B1), Def 5.19 p.30]
   I3 white Frobenius: (coadd (x) id);(id (x) add) = add;coadd
      = (id (x) coadd);(add (x) id) (2->2) [= W3 = B4]
   I4 black Frobenius: (copy (x) id);(id (x) cocopy) = cocopy;copy
      = (id (x) copy);(cocopy (x) id) (2->2) [= W4 = B3]
   I5 white/black cup: zero;coadd = blackunit;copy;(id (x) antipode) (0->2)
      [= W5; antipode = scalar -1; figure puts the antipode on the lower leg,
      leg choice interderivable via A5]
   I6 white/black cap: add;cozero = (antipode (x) id);cocopy;discard (2->0)
      [= W6; figure draws the mirrored antipode (-1)-mirror, which equals -1
      only by derived law D3 p.13 / I1-I2 at l = -1; upper-leg placement per
      the figure]
   I7 white special: coadd;add = id (1->1) [new in Def 6.1; provable in IH^Cp]
   I8 black special: copy;cocopy = id (1->1) [new in Def 6.1; provable in
      IH^Sp; = derived (D11) there]
   Field variant (Remark 6.3 p.32 = thesis Remark 3.45): over a field one may
   replace I1+I2 by the single family INV_k: k-mirror = scalar k^{-1} (1->1)
   for k /= 0.  Either {I1, I2} or {INV_k} — pick one, don't ship both as
   primitive rows.  This seed ships {I1, I2}; INV is not a row here.

3. Omission ledger (present in the papers, correctly absent from the seed):
   (Hopf) copy;(id (x) antipode);add = discard;zero = copy;(antipode (x) id);add
     — derived (Remark 3.4 p.9): A18@(1,-1) + A17 + A11.  Ditto op.
   (W2) zero;cozero = id_0 and (B2) blackunit;discard = id_0 (the two bones)
     — derivable from I1-I8 (p.32, Appendix D).
   (W7) (k (x) id);cocopy = (id (x) k-mirror);cocopy;k and
   (W8) copy;(k-mirror (x) id) = k-mirror;copy;(id (x) k) (all k) — derivable
     (p.32, App D); B7/B8 = mirrors.  [W7 LHS/RHS verified in LinRel_Q incl.
     k = 0; W8 leg placement uncertain at the branch level, fixed only up to
     A5.]
   (B5) blackunit;copy = zero;coadd;(id (x) antipode-mirror) and
   (B6) cocopy;discard = (antipode-mirror (x) id);add;cozero — subsumed: from
     I5/I6 post-composing with (-1)-mirror and I1/I2 at l = -1.  Not listed in
     the paper's "missing equations" sentence; still theorems.
   (D1)-(D11) p.13-14 are derived laws (Appendix B), incl. D3 (both antipodes
     coincide) and D11 (= I8 inside IH^Sp).
   PID-vs-field: no relation is dropped for Q; the only field-specific change
     is the optional Remark-6.3 swap of I1/I2 for INV_k.  Divisibility rows
     exist nowhere — over a PID the same I1/I2 do the job; there is no extra
     "k divides" row family.
   Thesis-only alternative: IH^Sp may swap (W2) for (D11) (thesis App A.2.4)
     — not imported; irrelevant to the merged Def 6.1.
   Compact-closed cups/caps and their yanking: defined from generators
     (Sect. 5.1), never rows.

4. Pitfalls (transcribed):
   (a) Antipode: the scalar -1 box — primitive only qua member of the scalar
     family G9 (mirror in G10); the "two Hopf laws" are not rows anywhere
     (derived, Rem 3.4).  Forward and mirrored antipodes coincide only as
     derived law D3; a seed identifying them definitionally would be wrong at
     the raw-term level — here they are distinct cells
     (`scalarBox (-1)` vs `scalarBoxMirror (-1)`).
   (b) Nonzero-only rows: exactly I1 and I2 (or their INV_k replacement).  At
     l = 0 they are unsound in LinRel_Q: 0;0-mirror = total relation /= id.
     Every other scalar-indexed family (A11-A18 + ops, W7/W8/B7/B8) ranges
     over all of Q.  (The shipped I1/I2 instances use l = 2 /= 0.)
   (c) Scalar 0 corner: 0 is a primitive generator (both orientations); A17
     pins it to discard;zero (disconnect), A17op pins 0-mirror to
     cozero;blackunit.  The empty diagram is id_0 (monoidal unit), reached by
     A10/A10op as axioms and W2/B2 as theorems.  Do not "exclude 0 from the
     scalar family" — exclude it only from I1/I2/INV.
   (d) Errata: no published erratum/corrigendum found (search 2026-07; JPAA
     DOI 10.1016/j.jpaa.2016.06.002 lists none).  On-record subtleties:
     (i) Remark 3.4 says HA_Z is presented "by equations (A3)-(A10) and
     (A11)-(A18) with k in {-1,0,1}" — the (A3) lower bound looks like a typo
     for (A1) (A1/A2 not obviously derivable); uncertain, and immaterial to
     the Q-seed which uses full (A1)-(A18).  (ii) Thesis notes W2 <-> D11
     interchangeability (presentation non-canonicity, Sp-side only).
     (iii) Duncan-Dunne "Interacting Frobenius Algebras are Hopf" (LICS'16) is
     a generalization, not a correction.  (iv) Over the finite signature IH_Z
     is not finitely axiomatizable (I1/I2 need all primes) — Z-specific; for Q
     the scalar families are infinite schemas regardless.
   Arity discipline (machine-checked here by `ihsRowGateFires`): every I-row
   is homogeneous (both sides same m->n as listed); A-rows likewise; the only
   0->0 rows are A10/A10op (and derived bones).

Seed deviations from the census (also recorded on the row docstrings):
(i) scalar-indexed families are shipped at instances (k = 2, k1 = 2/k2 = 3,
l = 2, antipode -1) — the census families are infinite schemas and the
diagram-level general row is not `rfl`-decidable (see `ihsRowGateFires`); the
raw-compose general forms shipped are A14/A14op.  (ii) The Frobenius chains
I3/I4 are shipped as two rows each (left/right equation against the shared
right-hand side), matching the census count 46.  (iii) A12op is instantiated as
2-mirror;3-mirror = 6-mirror — the census mirror family is
k1-mirror;k2-mirror = (k1*k2)-mirror with both orders instances of the schema.
No other deviation. -/
def ihsCompletenessStatement : Prop :=
  (firstDiagram secondDiagram : IhsDiagram) ->
    IhsDiagramWF firstDiagram -> IhsDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram ->
    IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
      (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram) ->
    IhsConv firstDiagram secondDiagram

/-- Open: completeness (BSZ Theorem 6.4, IH_Q = LinRel_Q) would require that
every span-equal well-formed diagram pair on matching boundaries is derivable in
`IhsConv`; it is unproven pending the reachability / normal-form argument.  See
`ihsCompletenessStatement` for the relation census and blockers. -/
def ihsCompletenessIsProven : Bool := false

end FX1Poly.ComputerAlgebra
