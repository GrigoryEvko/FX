import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfSeed

/-! # LinearAlgebra/InteractingHopfWhisker — the IH_Q whisker congruence (WP-PROP-3 brick 3)

The PARALLEL (whisker) congruence for the IH_Q presentation seed, executing the
brick-2 route note on `ihsHasWhiskerCongruence` verbatim: (1) the TENSOR SPEC
`ihwTensorSpec` — blockwise pair-membership characterization of `ihsTensorRows`
in both directions, via the embed zero/add/scale lemmas and
`ihqMapRowsSpanFwd/Bwd`; (2) the tensor laws — congruence, units, associativity
up to span, and THE INTERCHANGE `ihwTensorComposeInterchange`; (3) the
whisker/pad rewriting step: `IhwWindowMove` (a committed seed row OR a layer
split — the exchange move), `IhwStep.pad` (a window move fired inside wire
whiskering plus before/after context layers), the congruence `IhwConv` with
soundness `ihwConvSound` (full `IhsConvBundle`, so the seed's refutation bridge
carries over as `ihwConvSpanEqB`), and the EMBEDDING `ihwConvOfSeedConv` of the
committed sequential congruence `IhsConv` into `IhwConv`; (4) fires — four
committed seed rows re-fired INSIDE nontrivial parallel contexts with kernel
span pins, a two-redex parallel derivation, a layer-split exchange fire, and
the carried-over FALSE controls.

Shape cloned from the F2 template
(`Polygraph/Omega/ZXPhaseFree/SpiderRelationSeed`, prefix `zxp`): every xor
telescope becomes an add telescope PLUS the scale leg the QnfRat carrier
demands (the `ihqMapRowsSpanFwd/Bwd` hypotheses were already in the embed
shape, per the brick-2 report).

SCOPE HONESTY: completeness (BSZ Theorem 6.4) is NOT touched — the committed
owner-false markers `ihsCompletenessIsProven` / `ihsCompletenessStatement`
stay byte-intact in the seed; the brick-4 route (normal-form census + the
gate-refutation pass against the BSZ Section 6 factorization BEFORE any
completeness induction) is recorded on `ihwHasWhiskerCongruence`.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfWhisker.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — row-list plumbing the substrate lacks -/

/-- `ihqCat` with the empty second block is the identity. -/
theorem ihwCatNilRight : (row : List QnfRat) -> ihqCat row [] = row
  | [] => rfl
  | headCoeff :: restCoeffs =>
      congrArg (fun innerRow => headCoeff :: innerRow) (ihwCatNilRight restCoeffs)

/-- `ihqCat` is associative. -/
theorem ihwCatAssoc : (firstRow secondRow thirdRow : List QnfRat) ->
    ihqCat (ihqCat firstRow secondRow) thirdRow
      = ihqCat firstRow (ihqCat secondRow thirdRow)
  | [], _secondRow, _thirdRow => rfl
  | headCoeff :: restCoeffs, secondRow, thirdRow =>
      congrArg (fun innerRow => headCoeff :: innerRow)
        (ihwCatAssoc restCoeffs secondRow thirdRow)

/-- Width-index transport for `IhqMemSpan`. -/
theorem ihwMemSpanCast {firstWidth secondWidth : Nat} {rows : List (List QnfRat)}
    {vector : List QnfRat} (hWidthEq : firstWidth = secondWidth)
    (hMem : IhqMemSpan firstWidth rows vector) : IhqMemSpan secondWidth rows vector := by
  rw [<- hWidthEq]
  exact hMem

/-- Boundary-index transport for `IhqPairMem`. -/
theorem ihwPairMemCast {domWidth domWidth2 codWidth codWidth2 : Nat}
    {rows : List (List QnfRat)} {domVec codVec : List QnfRat}
    (hDomEq : domWidth = domWidth2) (hCodEq : codWidth = codWidth2) :
    IhqPairMem domWidth codWidth rows domVec codVec
      <-> IhqPairMem domWidth2 codWidth2 rows domVec codVec := by
  rw [hDomEq, hCodEq]

/-- The zero-width identity relation has no generators. -/
theorem ihwIdRowsZeroIsNil : ihqIdRows 0 = [] := rfl

/-- The wire cell's generator matrix IS the width-one identity relation. -/
theorem ihwWireCellRowsAreIdOne : ihsCellRows IhsCell.wire = ihqIdRows 1 := rfl

/-! ## Stage 1 — the tensor embeds are linear (T1 support)

The zero/add/scale lemmas for `ihsTensorEmbedFirst`/`ihsTensorEmbedSecond` in
exactly the hypothesis shape `ihqMapRowsSpanFwd/Bwd` demand, plus the length
lemmas and the block-recombination lemma `ihwTensorEmbedAddBlocks`. -/

theorem ihwTensorEmbedFirstLength (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (rowPair : List QnfRat)
    (hRowLen : rowPair.length = firstDomWidth + firstCodWidth) :
    (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth rowPair).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) := by
  show (ihqCat (ihqTakeN firstDomWidth rowPair)
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth)))).length
    = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
  rw [ihqCatLength, ihqCatLength, ihqCatLength,
    ihqTakeNLength rowPair firstDomWidth firstCodWidth hRowLen,
    ihqDropNLength rowPair firstDomWidth firstCodWidth hRowLen,
    ihqZeroRowLength, ihqZeroRowLength]

theorem ihwTensorEmbedFirstZero (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) :
    ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
        (ihqZeroRow (firstDomWidth + firstCodWidth))
      = ihqZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))) := by
  show ihqCat (ihqTakeN firstDomWidth (ihqZeroRow (firstDomWidth + firstCodWidth)))
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth (ihqZeroRow (firstDomWidth + firstCodWidth)))
          (ihqZeroRow secondCodWidth)))
    = ihqZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
  rw [ihqTakeNZeroRowExact firstDomWidth firstCodWidth,
    ihqDropNZeroRowExact firstDomWidth firstCodWidth,
    ihqCatZeroZero firstCodWidth secondCodWidth,
    ihqCatZeroZero secondDomWidth (firstCodWidth + secondCodWidth),
    ihqCatZeroZero firstDomWidth (secondDomWidth + (firstCodWidth + secondCodWidth))]

theorem ihwTensorEmbedFirstAdd (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = firstDomWidth + firstCodWidth)
    (hSecondLen : secondPair.length = firstDomWidth + firstCodWidth) :
    ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
        (ihqRowAdd firstPair secondPair)
      = ihqRowAdd
          (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth firstPair)
          (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth secondPair) := by
  have hTakeLens : (ihqTakeN firstDomWidth firstPair).length
      = (ihqTakeN firstDomWidth secondPair).length := by
    rw [ihqTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen,
      ihqTakeNLength secondPair firstDomWidth firstCodWidth hSecondLen]
  have hDropLens : (ihqDropN firstDomWidth firstPair).length
      = (ihqDropN firstDomWidth secondPair).length := by
    rw [ihqDropNLength firstPair firstDomWidth firstCodWidth hFirstLen,
      ihqDropNLength secondPair firstDomWidth firstCodWidth hSecondLen]
  show ihqCat (ihqTakeN firstDomWidth (ihqRowAdd firstPair secondPair))
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth (ihqRowAdd firstPair secondPair))
          (ihqZeroRow secondCodWidth)))
    = ihqRowAdd
        (ihqCat (ihqTakeN firstDomWidth firstPair)
          (ihqCat (ihqZeroRow secondDomWidth)
            (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth))))
        (ihqCat (ihqTakeN firstDomWidth secondPair)
          (ihqCat (ihqZeroRow secondDomWidth)
            (ihqCat (ihqDropN firstDomWidth secondPair) (ihqZeroRow secondCodWidth))))
  rw [ihqTakeNAdd firstDomWidth firstPair secondPair,
    ihqDropNAdd firstDomWidth firstPair secondPair,
    ihqRowAddCat (ihqTakeN firstDomWidth firstPair)
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth)))
      (ihqTakeN firstDomWidth secondPair)
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth secondPair) (ihqZeroRow secondCodWidth)))
      hTakeLens,
    ihqRowAddCat (ihqZeroRow secondDomWidth)
      (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth))
      (ihqZeroRow secondDomWidth)
      (ihqCat (ihqDropN firstDomWidth secondPair) (ihqZeroRow secondCodWidth)) rfl,
    ihqRowAddCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth)
      (ihqDropN firstDomWidth secondPair) (ihqZeroRow secondCodWidth) hDropLens,
    ihqRowAddZeroLeft (ihqZeroRow secondDomWidth) secondDomWidth
      (ihqZeroRowLength secondDomWidth),
    ihqRowAddZeroLeft (ihqZeroRow secondCodWidth) secondCodWidth
      (ihqZeroRowLength secondCodWidth)]

theorem ihwTensorEmbedFirstScale (firstDomWidth _firstCodWidth secondDomWidth
    secondCodWidth : Nat) (scalar : QnfRat) (rowPair : List QnfRat) :
    ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
        (ihqRowScale scalar rowPair)
      = ihqRowScale scalar
          (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth rowPair) := by
  show ihqCat (ihqTakeN firstDomWidth (ihqRowScale scalar rowPair))
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth (ihqRowScale scalar rowPair))
          (ihqZeroRow secondCodWidth)))
    = ihqRowScale scalar
        (ihqCat (ihqTakeN firstDomWidth rowPair)
          (ihqCat (ihqZeroRow secondDomWidth)
            (ihqCat (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth))))
  rw [ihqTakeNScale scalar firstDomWidth rowPair,
    ihqDropNScale scalar firstDomWidth rowPair,
    ihqRowScaleCat scalar (ihqTakeN firstDomWidth rowPair)
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth))),
    ihqRowScaleCat scalar (ihqZeroRow secondDomWidth)
      (ihqCat (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth)),
    ihqRowScaleCat scalar (ihqDropN firstDomWidth rowPair) (ihqZeroRow secondCodWidth),
    ihqRowScaleZeroRow scalar secondDomWidth, ihqRowScaleZeroRow scalar secondCodWidth]

theorem ihwTensorEmbedSecondLength (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (rowPair : List QnfRat)
    (hRowLen : rowPair.length = secondDomWidth + secondCodWidth) :
    (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth rowPair).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) := by
  show (ihqCat (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth rowPair)
        (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair)))).length
    = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
  rw [ihqCatLength, ihqCatLength, ihqCatLength,
    ihqTakeNLength rowPair secondDomWidth secondCodWidth hRowLen,
    ihqDropNLength rowPair secondDomWidth secondCodWidth hRowLen,
    ihqZeroRowLength, ihqZeroRowLength]

theorem ihwTensorEmbedSecondZero (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) :
    ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
        (ihqZeroRow (secondDomWidth + secondCodWidth))
      = ihqZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))) := by
  show ihqCat (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth (ihqZeroRow (secondDomWidth + secondCodWidth)))
        (ihqCat (ihqZeroRow firstCodWidth)
          (ihqDropN secondDomWidth (ihqZeroRow (secondDomWidth + secondCodWidth)))))
    = ihqZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
  rw [ihqTakeNZeroRowExact secondDomWidth secondCodWidth,
    ihqDropNZeroRowExact secondDomWidth secondCodWidth,
    ihqCatZeroZero firstCodWidth secondCodWidth,
    ihqCatZeroZero secondDomWidth (firstCodWidth + secondCodWidth),
    ihqCatZeroZero firstDomWidth (secondDomWidth + (firstCodWidth + secondCodWidth))]

theorem ihwTensorEmbedSecondAdd (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = secondDomWidth + secondCodWidth)
    (hSecondLen : secondPair.length = secondDomWidth + secondCodWidth) :
    ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
        (ihqRowAdd firstPair secondPair)
      = ihqRowAdd
          (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth firstPair)
          (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth secondPair) := by
  have hTakeLens : (ihqTakeN secondDomWidth firstPair).length
      = (ihqTakeN secondDomWidth secondPair).length := by
    rw [ihqTakeNLength firstPair secondDomWidth secondCodWidth hFirstLen,
      ihqTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen]
  show ihqCat (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth (ihqRowAdd firstPair secondPair))
        (ihqCat (ihqZeroRow firstCodWidth)
          (ihqDropN secondDomWidth (ihqRowAdd firstPair secondPair))))
    = ihqRowAdd
        (ihqCat (ihqZeroRow firstDomWidth)
          (ihqCat (ihqTakeN secondDomWidth firstPair)
            (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth firstPair))))
        (ihqCat (ihqZeroRow firstDomWidth)
          (ihqCat (ihqTakeN secondDomWidth secondPair)
            (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair))))
  rw [ihqTakeNAdd secondDomWidth firstPair secondPair,
    ihqDropNAdd secondDomWidth firstPair secondPair,
    ihqRowAddCat (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth firstPair)
        (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth firstPair)))
      (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth secondPair)
        (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair))) rfl,
    ihqRowAddCat (ihqTakeN secondDomWidth firstPair)
      (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth firstPair))
      (ihqTakeN secondDomWidth secondPair)
      (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair)) hTakeLens,
    ihqRowAddCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth firstPair)
      (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair) rfl,
    ihqRowAddZeroLeft (ihqZeroRow firstDomWidth) firstDomWidth
      (ihqZeroRowLength firstDomWidth),
    ihqRowAddZeroLeft (ihqZeroRow firstCodWidth) firstCodWidth
      (ihqZeroRowLength firstCodWidth)]

theorem ihwTensorEmbedSecondScale (firstDomWidth firstCodWidth secondDomWidth
    _secondCodWidth : Nat) (scalar : QnfRat) (rowPair : List QnfRat) :
    ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
        (ihqRowScale scalar rowPair)
      = ihqRowScale scalar
          (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth rowPair) := by
  show ihqCat (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth (ihqRowScale scalar rowPair))
        (ihqCat (ihqZeroRow firstCodWidth)
          (ihqDropN secondDomWidth (ihqRowScale scalar rowPair))))
    = ihqRowScale scalar
        (ihqCat (ihqZeroRow firstDomWidth)
          (ihqCat (ihqTakeN secondDomWidth rowPair)
            (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair))))
  rw [ihqTakeNScale scalar secondDomWidth rowPair,
    ihqDropNScale scalar secondDomWidth rowPair,
    ihqRowScaleCat scalar (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth rowPair)
        (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair))),
    ihqRowScaleCat scalar (ihqTakeN secondDomWidth rowPair)
      (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair)),
    ihqRowScaleCat scalar (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth rowPair),
    ihqRowScaleZeroRow scalar firstDomWidth, ihqRowScaleZeroRow scalar firstCodWidth]

/-- The sum of the two tensor embeddings recombines into interleaved blocks. -/
theorem ihwTensorEmbedAddBlocks (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = firstDomWidth + firstCodWidth)
    (hSecondLen : secondPair.length = secondDomWidth + secondCodWidth) :
    ihqRowAdd (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth firstPair)
        (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth secondPair)
      = ihqCat (ihqTakeN firstDomWidth firstPair)
          (ihqCat (ihqTakeN secondDomWidth secondPair)
            (ihqCat (ihqDropN firstDomWidth firstPair)
              (ihqDropN secondDomWidth secondPair))) := by
  show ihqRowAdd
      (ihqCat (ihqTakeN firstDomWidth firstPair)
        (ihqCat (ihqZeroRow secondDomWidth)
          (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth))))
      (ihqCat (ihqZeroRow firstDomWidth)
        (ihqCat (ihqTakeN secondDomWidth secondPair)
          (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair))))
    = ihqCat (ihqTakeN firstDomWidth firstPair)
        (ihqCat (ihqTakeN secondDomWidth secondPair)
          (ihqCat (ihqDropN firstDomWidth firstPair) (ihqDropN secondDomWidth secondPair)))
  have hOuterLens : (ihqTakeN firstDomWidth firstPair).length
      = (ihqZeroRow firstDomWidth).length := by
    rw [ihqTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen, ihqZeroRowLength]
  have hMidLens : (ihqZeroRow secondDomWidth).length
      = (ihqTakeN secondDomWidth secondPair).length := by
    rw [ihqTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen,
      ihqZeroRowLength]
  have hInnerLens : (ihqDropN firstDomWidth firstPair).length
      = (ihqZeroRow firstCodWidth).length := by
    rw [ihqDropNLength firstPair firstDomWidth firstCodWidth hFirstLen, ihqZeroRowLength]
  rw [ihqRowAddCat (ihqTakeN firstDomWidth firstPair)
      (ihqCat (ihqZeroRow secondDomWidth)
        (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth)))
      (ihqZeroRow firstDomWidth)
      (ihqCat (ihqTakeN secondDomWidth secondPair)
        (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair)))
      hOuterLens,
    ihqRowAddCat (ihqZeroRow secondDomWidth)
      (ihqCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth))
      (ihqTakeN secondDomWidth secondPair)
      (ihqCat (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair)) hMidLens,
    ihqRowAddCat (ihqDropN firstDomWidth firstPair) (ihqZeroRow secondCodWidth)
      (ihqZeroRow firstCodWidth) (ihqDropN secondDomWidth secondPair) hInnerLens,
    ihqRowAddZeroRight (ihqTakeN firstDomWidth firstPair) firstDomWidth
      (ihqTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen),
    ihqRowAddZeroLeft (ihqTakeN secondDomWidth secondPair) secondDomWidth
      (ihqTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen),
    ihqRowAddZeroRight (ihqDropN firstDomWidth firstPair) firstCodWidth
      (ihqDropNLength firstPair firstDomWidth firstCodWidth hFirstLen),
    ihqRowAddZeroLeft (ihqDropN secondDomWidth secondPair) secondCodWidth
      (ihqDropNLength secondPair secondDomWidth secondCodWidth hSecondLen)]

/-! ## Stage 2 — THE TENSOR SPEC (T1) -/

/-- **THE TENSOR SPEC**: the interleaved direct sum relates exactly blockwise —
`IhqPairMem` of the tensor iff componentwise `IhqPairMem`, both directions. -/
theorem ihwTensorSpec (firstDomWidth firstCodWidth secondDomWidth secondCodWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : IhqAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (domVec codVec : List QnfRat) :
    IhqPairMem (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows) domVec codVec
    <-> Exists fun firstDomVec => Exists fun secondDomVec =>
        Exists fun firstCodVec => Exists fun secondCodVec =>
          domVec = ihqCat firstDomVec secondDomVec
            /\ codVec = ihqCat firstCodVec secondCodVec
            /\ IhqPairMem firstDomWidth firstCodWidth firstRows firstDomVec firstCodVec
            /\ IhqPairMem secondDomWidth secondCodWidth secondRows
                secondDomVec secondCodVec := by
  have hLeftAll : IhqAllWidth
      (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
      (ihqMapRows (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth)
        firstRows) :=
    ihqMapRowsWidth _ (fun rowPair hRowLen => ihwTensorEmbedFirstLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth rowPair hRowLen) firstRows hFirstAll
  have hRightAll : IhqAllWidth
      (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
      (ihqMapRows (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth)
        secondRows) :=
    ihqMapRowsWidth _ (fun rowPair hRowLen => ihwTensorEmbedSecondLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth rowPair hRowLen) secondRows hSecondAll
  have hBracket : (firstDomWidth + secondDomWidth) + (firstCodWidth + secondCodWidth)
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) :=
    Nat.add_assoc firstDomWidth secondDomWidth (firstCodWidth + secondCodWidth)
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomLen : domVec.length = firstDomWidth + secondDomWidth := hPair.left
    have hCodLen : codVec.length = firstCodWidth + secondCodWidth := hPair.right.left
    have hMem := ihwMemSpanCast hBracket hPair.right.right
    have hSplit := ihqCatRowsSpanSplitFwd hLeftAll hRightAll hMem
    cases hSplit with
    | intro leftPart hRightPack =>
        cases hRightPack with
        | intro rightPart hParts =>
            have hLeftInv := ihqMapRowsSpanFwd
              (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth)
              (ihwTensorEmbedFirstZero firstDomWidth firstCodWidth secondDomWidth
                secondCodWidth)
              (fun firstRow secondRow hFirstLen hSecondLen =>
                ihwTensorEmbedFirstAdd firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth firstRow secondRow hFirstLen hSecondLen)
              (fun scalar rowPair _hRowLen =>
                ihwTensorEmbedFirstScale firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth scalar rowPair)
              hFirstAll hParts.left
            have hRightInv := ihqMapRowsSpanFwd
              (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth)
              (ihwTensorEmbedSecondZero firstDomWidth firstCodWidth secondDomWidth
                secondCodWidth)
              (fun firstRow secondRow hFirstLen hSecondLen =>
                ihwTensorEmbedSecondAdd firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth firstRow secondRow hFirstLen hSecondLen)
              (fun scalar rowPair _hRowLen =>
                ihwTensorEmbedSecondScale firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth scalar rowPair)
              hSecondAll hParts.right.left
            cases hLeftInv with
            | intro firstPair hFirstBoth =>
                cases hRightInv with
                | intro secondPair hSecondBoth =>
                    have hFirstPairLen : firstPair.length
                        = firstDomWidth + firstCodWidth :=
                      ihqMemSpanWidth hFirstAll hFirstBoth.left
                    have hSecondPairLen : secondPair.length
                        = secondDomWidth + secondCodWidth :=
                      ihqMemSpanWidth hSecondAll hSecondBoth.left
                    have hBlocks : ihqCat domVec codVec
                        = ihqCat (ihqTakeN firstDomWidth firstPair)
                            (ihqCat (ihqTakeN secondDomWidth secondPair)
                              (ihqCat (ihqDropN firstDomWidth firstPair)
                                (ihqDropN secondDomWidth secondPair))) := by
                      rw [hParts.right.right, hFirstBoth.right, hSecondBoth.right]
                      exact ihwTensorEmbedAddBlocks firstDomWidth firstCodWidth
                        secondDomWidth secondCodWidth firstPair secondPair
                        hFirstPairLen hSecondPairLen
                    have hDomSplit : ihqCat (ihqTakeN firstDomWidth domVec)
                        (ihqDropN firstDomWidth domVec) = domVec :=
                      ihqCatTakeDrop domVec firstDomWidth secondDomWidth hDomLen
                    have hFlat : ihqCat (ihqTakeN firstDomWidth domVec)
                        (ihqCat (ihqDropN firstDomWidth domVec) codVec)
                        = ihqCat (ihqTakeN firstDomWidth firstPair)
                            (ihqCat (ihqTakeN secondDomWidth secondPair)
                              (ihqCat (ihqDropN firstDomWidth firstPair)
                                (ihqDropN secondDomWidth secondPair))) := by
                      rw [<- ihwCatAssoc (ihqTakeN firstDomWidth domVec)
                        (ihqDropN firstDomWidth domVec) codVec, hDomSplit]
                      exact hBlocks
                    have hFirstSplit := ihqCatInj (ihqTakeN firstDomWidth domVec)
                      (ihqCat (ihqDropN firstDomWidth domVec) codVec)
                      (ihqTakeN firstDomWidth firstPair)
                      (ihqCat (ihqTakeN secondDomWidth secondPair)
                        (ihqCat (ihqDropN firstDomWidth firstPair)
                          (ihqDropN secondDomWidth secondPair)))
                      (by rw [ihqTakeNLength domVec firstDomWidth secondDomWidth hDomLen,
                        ihqTakeNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen])
                      hFlat
                    have hSecondSplit := ihqCatInj (ihqDropN firstDomWidth domVec) codVec
                      (ihqTakeN secondDomWidth secondPair)
                      (ihqCat (ihqDropN firstDomWidth firstPair)
                        (ihqDropN secondDomWidth secondPair))
                      (by rw [ihqDropNLength domVec firstDomWidth secondDomWidth hDomLen,
                        ihqTakeNLength secondPair secondDomWidth secondCodWidth
                          hSecondPairLen])
                      hFirstSplit.right
                    refine Exists.intro (ihqTakeN firstDomWidth firstPair)
                      (Exists.intro (ihqTakeN secondDomWidth secondPair)
                        (Exists.intro (ihqDropN firstDomWidth firstPair)
                          (Exists.intro (ihqDropN secondDomWidth secondPair)
                            (And.intro ?_ (And.intro hSecondSplit.right
                              (And.intro ?_ ?_))))))
                    · rw [<- hFirstSplit.left, <- hSecondSplit.left]
                      exact hDomSplit.symm
                    · refine And.intro
                        (ihqTakeNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen)
                        (And.intro (ihqDropNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen) ?_)
                      rw [ihqCatTakeDrop firstPair firstDomWidth firstCodWidth
                        hFirstPairLen]
                      exact hFirstBoth.left
                    · refine And.intro
                        (ihqTakeNLength secondPair secondDomWidth secondCodWidth
                          hSecondPairLen)
                        (And.intro (ihqDropNLength secondPair secondDomWidth
                          secondCodWidth hSecondPairLen) ?_)
                      rw [ihqCatTakeDrop secondPair secondDomWidth secondCodWidth
                        hSecondPairLen]
                      exact hSecondBoth.left
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hDomEq := hFacts.left
                    have hCodEq := hFacts.right.left
                    have hFirstPair := hFacts.right.right.left
                    have hSecondPair := hFacts.right.right.right
                    have hFdLen : firstDomVec.length = firstDomWidth := hFirstPair.left
                    have hFcLen : firstCodVec.length = firstCodWidth :=
                      hFirstPair.right.left
                    have hSdLen : secondDomVec.length = secondDomWidth :=
                      hSecondPair.left
                    have hScLen : secondCodVec.length = secondCodWidth :=
                      hSecondPair.right.left
                    have hFirstCatLen : (ihqCat firstDomVec firstCodVec).length
                        = firstDomWidth + firstCodWidth := by
                      rw [ihqCatLength, hFdLen, hFcLen]
                    have hSecondCatLen : (ihqCat secondDomVec secondCodVec).length
                        = secondDomWidth + secondCodWidth := by
                      rw [ihqCatLength, hSdLen, hScLen]
                    have hStackVecEq : ihqRowAdd
                        (ihsTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
                          (ihqCat firstDomVec firstCodVec))
                        (ihsTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
                          (ihqCat secondDomVec secondCodVec))
                      = ihqCat firstDomVec (ihqCat secondDomVec
                          (ihqCat firstCodVec secondCodVec)) := by
                      rw [ihwTensorEmbedAddBlocks firstDomWidth firstCodWidth
                          secondDomWidth secondCodWidth _ _ hFirstCatLen hSecondCatLen,
                        ihqTakeNCatExact firstDomVec firstCodVec firstDomWidth hFdLen,
                        ihqDropNCatExact firstDomVec firstCodVec firstDomWidth hFdLen,
                        ihqTakeNCatExact secondDomVec secondCodVec secondDomWidth hSdLen,
                        ihqDropNCatExact secondDomVec secondCodVec secondDomWidth hSdLen]
                    have hInStack : IhqMemSpan
                        (firstDomWidth + (secondDomWidth
                          + (firstCodWidth + secondCodWidth)))
                        (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth
                          secondCodWidth firstRows secondRows)
                        (ihqCat firstDomVec (ihqCat secondDomVec
                          (ihqCat firstCodVec secondCodVec))) := by
                      rw [<- hStackVecEq]
                      refine ihqMemSpanAddClosed (ihqCatRowsWidth _ _ hLeftAll hRightAll)
                        ?_ ?_
                      · exact ihqCatRowsSpanLeft
                          (ihqMapRowsSpanBwd _
                            (ihwTensorEmbedFirstZero firstDomWidth firstCodWidth
                              secondDomWidth secondCodWidth)
                            (fun firstRow secondRow hFirstLen hSecondLen =>
                              ihwTensorEmbedFirstAdd firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth firstRow secondRow
                                hFirstLen hSecondLen)
                            (fun scalar rowPair _hRowLen =>
                              ihwTensorEmbedFirstScale firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth scalar rowPair)
                            hFirstAll hFirstPair.right.right)
                      · exact ihqCatRowsSpanRight
                          (ihqMapRowsSpanBwd _
                            (ihwTensorEmbedSecondZero firstDomWidth firstCodWidth
                              secondDomWidth secondCodWidth)
                            (fun firstRow secondRow hFirstLen hSecondLen =>
                              ihwTensorEmbedSecondAdd firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth firstRow secondRow
                                hFirstLen hSecondLen)
                            (fun scalar rowPair _hRowLen =>
                              ihwTensorEmbedSecondScale firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth scalar rowPair)
                            hSecondAll hSecondPair.right.right)
                    refine And.intro ?_ (And.intro ?_ ?_)
                    · rw [hDomEq, ihqCatLength, hFdLen, hSdLen]
                    · rw [hCodEq, ihqCatLength, hFcLen, hScLen]
                    · refine ihwMemSpanCast hBracket.symm ?_
                      rw [hDomEq, hCodEq,
                        ihwCatAssoc firstDomVec secondDomVec
                          (ihqCat firstCodVec secondCodVec)]
                      exact hInStack

/-! ## Stage 3 — the tensor laws (T2) -/

/-- Tensor respects span equality on both sides. -/
theorem ihwTensorRowsCong (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat)
    {firstRows firstRows2 secondRows secondRows2 : List (List QnfRat)}
    (hFirstAll : IhqAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hFirstAll2 : IhqAllWidth (firstDomWidth + firstCodWidth) firstRows2)
    (hSecondAll : IhqAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (hSecondAll2 : IhqAllWidth (secondDomWidth + secondCodWidth) secondRows2)
    (hLeft : IhsRelEquiv firstDomWidth firstCodWidth firstRows firstRows2)
    (hRight : IhsRelEquiv secondDomWidth secondCodWidth secondRows secondRows2) :
    IhsRelEquiv (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows)
      (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows2 secondRows2) := by
  intro domVec codVec
  refine Iff.trans (ihwTensorSpec firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth firstRows secondRows hFirstAll hSecondAll domVec codVec)
    (Iff.trans ?_ (ihwTensorSpec firstDomWidth firstCodWidth secondDomWidth
      secondCodWidth firstRows2 secondRows2 hFirstAll2 hSecondAll2 domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    exact Exists.intro firstDomVec (Exists.intro secondDomVec
                      (Exists.intro firstCodVec (Exists.intro secondCodVec
                        (And.intro hFacts.left (And.intro hFacts.right.left
                          (And.intro
                            ((hLeft firstDomVec firstCodVec).mp
                              hFacts.right.right.left)
                            ((hRight secondDomVec secondCodVec).mp
                              hFacts.right.right.right)))))))
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    exact Exists.intro firstDomVec (Exists.intro secondDomVec
                      (Exists.intro firstCodVec (Exists.intro secondCodVec
                        (And.intro hFacts.left (And.intro hFacts.right.left
                          (And.intro
                            ((hLeft firstDomVec firstCodVec).mpr
                              hFacts.right.right.left)
                            ((hRight secondDomVec secondCodVec).mpr
                              hFacts.right.right.right)))))))

/-- Tensoring two identities is the identity of the sum boundary. -/
theorem ihwTensorIdSum (firstWidth secondWidth : Nat) :
    IhsRelEquiv (firstWidth + secondWidth) (firstWidth + secondWidth)
      (ihsTensorRows firstWidth firstWidth secondWidth secondWidth
        (ihqIdRows firstWidth) (ihqIdRows secondWidth))
      (ihqIdRows (firstWidth + secondWidth)) := by
  intro domVec codVec
  refine Iff.trans (ihwTensorSpec firstWidth firstWidth secondWidth secondWidth
    (ihqIdRows firstWidth) (ihqIdRows secondWidth)
    (ihqIdRowsWidth firstWidth) (ihqIdRowsWidth secondWidth) domVec codVec)
    (Iff.trans ?_ (ihsIdSpec (firstWidth + secondWidth) domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFirstSame := (ihsIdSpec firstWidth firstDomVec firstCodVec).mp
                      hFacts.right.right.left
                    have hSecondSame := (ihsIdSpec secondWidth secondDomVec
                      secondCodVec).mp hFacts.right.right.right
                    refine And.intro ?_ ?_
                    · rw [hFacts.left, hFacts.right.left, hFirstSame.left,
                        hSecondSame.left]
                    · rw [hFacts.left, ihqCatLength, hFirstSame.right, hSecondSame.right]
  · intro hSame
    cases hSame with
    | intro hEqVecs hDomLen =>
        refine Exists.intro (ihqTakeN firstWidth domVec)
          (Exists.intro (ihqDropN firstWidth domVec)
            (Exists.intro (ihqTakeN firstWidth domVec)
              (Exists.intro (ihqDropN firstWidth domVec)
                (And.intro (ihqCatTakeDrop domVec firstWidth secondWidth hDomLen).symm
                  (And.intro ?_ (And.intro ?_ ?_))))))
        · rw [<- hEqVecs]
          exact (ihqCatTakeDrop domVec firstWidth secondWidth hDomLen).symm
        · exact (ihsIdSpec firstWidth (ihqTakeN firstWidth domVec)
            (ihqTakeN firstWidth domVec)).mpr
            (And.intro rfl (ihqTakeNLength domVec firstWidth secondWidth hDomLen))
        · exact (ihsIdSpec secondWidth (ihqDropN firstWidth domVec)
            (ihqDropN firstWidth domVec)).mpr
            (And.intro rfl (ihqDropNLength domVec firstWidth secondWidth hDomLen))

/-- Tensor with the empty boundary on the left is the identity operation
(`ihqIdRows 0 = []`, see `ihwIdRowsZeroIsNil`). -/
theorem ihwTensorUnitLeft (domWidth codWidth : Nat) (rows : List (List QnfRat))
    (hAll : IhqAllWidth (domWidth + codWidth) rows) :
    IhsRelEquiv domWidth codWidth
      (ihsTensorRows 0 0 domWidth codWidth [] rows) rows := by
  intro domVec codVec
  refine Iff.trans (ihwPairMemCast (Nat.zero_add domWidth).symm
    (Nat.zero_add codWidth).symm) ?_
  refine Iff.trans (ihwTensorSpec 0 0 domWidth codWidth [] rows
    IhqAllWidth.nil hAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFdNil := ihsLengthZeroNil firstDomVec
                      hFacts.right.right.left.left
                    have hFcNil := ihsLengthZeroNil firstCodVec
                      hFacts.right.right.left.right.left
                    have hDomIs : domVec = secondDomVec := by
                      rw [hFacts.left, hFdNil]
                      rfl
                    have hCodIs : codVec = secondCodVec := by
                      rw [hFacts.right.left, hFcNil]
                      rfl
                    rw [hDomIs, hCodIs]
                    exact hFacts.right.right.right
  · intro hPair
    refine Exists.intro [] (Exists.intro domVec (Exists.intro [] (Exists.intro codVec
      (And.intro rfl (And.intro rfl (And.intro ?_ hPair))))))
    exact And.intro rfl (And.intro rfl IhqMemSpan.zero)

/-- Tensor with the empty boundary on the right is the identity operation. -/
theorem ihwTensorUnitRight (domWidth codWidth : Nat) (rows : List (List QnfRat))
    (hAll : IhqAllWidth (domWidth + codWidth) rows) :
    IhsRelEquiv domWidth codWidth
      (ihsTensorRows domWidth codWidth 0 0 rows []) rows := by
  intro domVec codVec
  refine Iff.trans (ihwTensorSpec domWidth codWidth 0 0 rows []
    hAll IhqAllWidth.nil domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hSdNil := ihsLengthZeroNil secondDomVec
                      hFacts.right.right.right.left
                    have hScNil := ihsLengthZeroNil secondCodVec
                      hFacts.right.right.right.right.left
                    have hDomIs : domVec = firstDomVec := by
                      rw [hFacts.left, hSdNil]
                      exact ihwCatNilRight firstDomVec
                    have hCodIs : codVec = firstCodVec := by
                      rw [hFacts.right.left, hScNil]
                      exact ihwCatNilRight firstCodVec
                    rw [hDomIs, hCodIs]
                    exact hFacts.right.right.left
  · intro hPair
    refine Exists.intro domVec (Exists.intro [] (Exists.intro codVec (Exists.intro []
      (And.intro (ihwCatNilRight domVec).symm
        (And.intro (ihwCatNilRight codVec).symm (And.intro hPair ?_))))))
    exact And.intro rfl (And.intro rfl IhqMemSpan.zero)

/-- Tensor is associative up to span equality (stated at the left-nested boundary). -/
theorem ihwTensorRowsAssoc (firstDomWidth firstCodWidth secondDomWidth secondCodWidth
    thirdDomWidth thirdCodWidth : Nat)
    (firstRows secondRows thirdRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : IhqAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (hThirdAll : IhqAllWidth (thirdDomWidth + thirdCodWidth) thirdRows) :
    IhsRelEquiv ((firstDomWidth + secondDomWidth) + thirdDomWidth)
      ((firstCodWidth + secondCodWidth) + thirdCodWidth)
      (ihsTensorRows (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
        thirdDomWidth thirdCodWidth
        (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
          firstRows secondRows) thirdRows)
      (ihsTensorRows firstDomWidth firstCodWidth (secondDomWidth + thirdDomWidth)
        (secondCodWidth + thirdCodWidth) firstRows
        (ihsTensorRows secondDomWidth secondCodWidth thirdDomWidth thirdCodWidth
          secondRows thirdRows)) := by
  have hLeftPairAll := ihsTensorRowsWidth firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth firstRows secondRows hFirstAll hSecondAll
  have hRightPairAll := ihsTensorRowsWidth secondDomWidth secondCodWidth thirdDomWidth
    thirdCodWidth secondRows thirdRows hSecondAll hThirdAll
  intro domVec codVec
  refine Iff.trans (ihwTensorSpec (firstDomWidth + secondDomWidth)
    (firstCodWidth + secondCodWidth) thirdDomWidth thirdCodWidth _ thirdRows
    hLeftPairAll hThirdAll domVec codVec) ?_
  refine Iff.trans ?_ (Iff.trans (ihwTensorSpec firstDomWidth firstCodWidth
    (secondDomWidth + thirdDomWidth) (secondCodWidth + thirdCodWidth) firstRows _
    hFirstAll hRightPairAll domVec codVec).symm
    (ihwPairMemCast (Nat.add_assoc firstDomWidth secondDomWidth thirdDomWidth).symm
      (Nat.add_assoc firstCodWidth secondCodWidth thirdCodWidth).symm))
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro pairDomVec hPack1 =>
        cases hPack1 with
        | intro thirdDomVec hPack2 =>
            cases hPack2 with
            | intro pairCodVec hPack3 =>
                cases hPack3 with
                | intro thirdCodVec hFacts =>
                    have hPairSplit := (ihwTensorSpec firstDomWidth firstCodWidth
                      secondDomWidth secondCodWidth firstRows secondRows hFirstAll
                      hSecondAll pairDomVec pairCodVec).mp hFacts.right.right.left
                    cases hPairSplit with
                    | intro firstDomVec hInner1 =>
                        cases hInner1 with
                        | intro secondDomVec hInner2 =>
                            cases hInner2 with
                            | intro firstCodVec hInner3 =>
                                cases hInner3 with
                                | intro secondCodVec hInnerFacts =>
                                    refine Exists.intro firstDomVec
                                      (Exists.intro (ihqCat secondDomVec thirdDomVec)
                                        (Exists.intro firstCodVec
                                          (Exists.intro
                                            (ihqCat secondCodVec thirdCodVec)
                                            (And.intro ?_ (And.intro ?_ (And.intro
                                              hInnerFacts.right.right.left ?_))))))
                                    · rw [hFacts.left, hInnerFacts.left]
                                      exact ihwCatAssoc firstDomVec secondDomVec
                                        thirdDomVec
                                    · rw [hFacts.right.left, hInnerFacts.right.left]
                                      exact ihwCatAssoc firstCodVec secondCodVec
                                        thirdCodVec
                                    · refine (ihwTensorSpec secondDomWidth secondCodWidth
                                        thirdDomWidth thirdCodWidth secondRows thirdRows
                                        hSecondAll hThirdAll _ _).mpr ?_
                                      exact Exists.intro secondDomVec
                                        (Exists.intro thirdDomVec
                                          (Exists.intro secondCodVec
                                            (Exists.intro thirdCodVec
                                              (And.intro rfl (And.intro rfl (And.intro
                                                hInnerFacts.right.right.right
                                                hFacts.right.right.right))))))
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro restDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro restCodVec hFacts =>
                    have hRestSplit := (ihwTensorSpec secondDomWidth secondCodWidth
                      thirdDomWidth thirdCodWidth secondRows thirdRows hSecondAll
                      hThirdAll restDomVec restCodVec).mp hFacts.right.right.right
                    cases hRestSplit with
                    | intro secondDomVec hInner1 =>
                        cases hInner1 with
                        | intro thirdDomVec hInner2 =>
                            cases hInner2 with
                            | intro secondCodVec hInner3 =>
                                cases hInner3 with
                                | intro thirdCodVec hInnerFacts =>
                                    refine Exists.intro
                                      (ihqCat firstDomVec secondDomVec)
                                      (Exists.intro thirdDomVec
                                        (Exists.intro
                                          (ihqCat firstCodVec secondCodVec)
                                          (Exists.intro thirdCodVec
                                            (And.intro ?_ (And.intro ?_ (And.intro
                                              ?_ hInnerFacts.right.right.right))))))
                                    · rw [hFacts.left, hInnerFacts.left,
                                        <- ihwCatAssoc firstDomVec secondDomVec
                                          thirdDomVec]
                                    · rw [hFacts.right.left, hInnerFacts.right.left,
                                        <- ihwCatAssoc firstCodVec secondCodVec
                                          thirdCodVec]
                                    · refine (ihwTensorSpec firstDomWidth firstCodWidth
                                        secondDomWidth secondCodWidth firstRows
                                        secondRows hFirstAll hSecondAll _ _).mpr ?_
                                      exact Exists.intro firstDomVec
                                        (Exists.intro secondDomVec
                                          (Exists.intro firstCodVec
                                            (Exists.intro secondCodVec
                                              (And.intro rfl (And.intro rfl (And.intro
                                                hFacts.right.right.left
                                                hInnerFacts.right.right.left))))))

/-- **THE INTERCHANGE LAW**: composing tensors is tensoring composites (up to span),
at matched boundaries. -/
theorem ihwTensorComposeInterchange (firstDomWidth firstMidWidth firstCodWidth
    secondDomWidth secondMidWidth secondCodWidth : Nat)
    (firstRows firstRows2 secondRows secondRows2 : List (List QnfRat))
    (hFirstAll : IhqAllWidth (firstDomWidth + firstMidWidth) firstRows)
    (hFirstAll2 : IhqAllWidth (firstMidWidth + firstCodWidth) firstRows2)
    (hSecondAll : IhqAllWidth (secondDomWidth + secondMidWidth) secondRows)
    (hSecondAll2 : IhqAllWidth (secondMidWidth + secondCodWidth) secondRows2) :
    IhsRelEquiv (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (ihqComposeRows (firstDomWidth + secondDomWidth)
        (firstMidWidth + secondMidWidth) (firstCodWidth + secondCodWidth)
        (ihsTensorRows firstDomWidth firstMidWidth secondDomWidth secondMidWidth
          firstRows secondRows)
        (ihsTensorRows firstMidWidth firstCodWidth secondMidWidth secondCodWidth
          firstRows2 secondRows2))
      (ihsTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        (ihqComposeRows firstDomWidth firstMidWidth firstCodWidth firstRows firstRows2)
        (ihqComposeRows secondDomWidth secondMidWidth secondCodWidth secondRows
          secondRows2)) := by
  have hTensorInAll := ihsTensorRowsWidth firstDomWidth firstMidWidth secondDomWidth
    secondMidWidth firstRows secondRows hFirstAll hSecondAll
  have hTensorOutAll := ihsTensorRowsWidth firstMidWidth firstCodWidth secondMidWidth
    secondCodWidth firstRows2 secondRows2 hFirstAll2 hSecondAll2
  have hComposeFirstAll := ihqComposeRowsWidth firstDomWidth firstMidWidth firstCodWidth
    firstRows firstRows2 hFirstAll hFirstAll2
  have hComposeSecondAll := ihqComposeRowsWidth secondDomWidth secondMidWidth
    secondCodWidth secondRows secondRows2 hSecondAll hSecondAll2
  intro domVec codVec
  refine Iff.trans (ihqComposeSpec (firstDomWidth + secondDomWidth)
    (firstMidWidth + secondMidWidth) (firstCodWidth + secondCodWidth) _ _
    hTensorInAll hTensorOutAll domVec codVec)
    (Iff.trans ?_ (ihwTensorSpec firstDomWidth firstCodWidth secondDomWidth
      secondCodWidth _ _ hComposeFirstAll hComposeSecondAll domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        have hInSplit := (ihwTensorSpec firstDomWidth firstMidWidth secondDomWidth
          secondMidWidth firstRows secondRows hFirstAll hSecondAll domVec midVec).mp
          hBoth.left
        cases hInSplit with
        | intro firstDomVec hPack1 =>
            cases hPack1 with
            | intro secondDomVec hPack2 =>
                cases hPack2 with
                | intro firstMidVec hPack3 =>
                    cases hPack3 with
                    | intro secondMidVec hInFacts =>
                        have hOutSplit := (ihwTensorSpec firstMidWidth firstCodWidth
                          secondMidWidth secondCodWidth firstRows2 secondRows2
                          hFirstAll2 hSecondAll2 midVec codVec).mp hBoth.right
                        cases hOutSplit with
                        | intro firstMidVec2 hQack1 =>
                            cases hQack1 with
                            | intro secondMidVec2 hQack2 =>
                                cases hQack2 with
                                | intro firstCodVec hQack3 =>
                                    cases hQack3 with
                                    | intro secondCodVec hOutFacts =>
                                        have hMidAligned : firstMidVec = firstMidVec2
                                            /\ secondMidVec = secondMidVec2 := by
                                          have hMidChain : ihqCat firstMidVec
                                              secondMidVec
                                            = ihqCat firstMidVec2 secondMidVec2 := by
                                            rw [<- hInFacts.right.left,
                                              <- hOutFacts.left]
                                          exact ihqCatInj firstMidVec secondMidVec
                                            firstMidVec2 secondMidVec2
                                            (by rw [hInFacts.right.right.left.right.left,
                                              hOutFacts.right.right.left.left])
                                            hMidChain
                                        refine Exists.intro firstDomVec
                                          (Exists.intro secondDomVec
                                            (Exists.intro firstCodVec
                                              (Exists.intro secondCodVec
                                                (And.intro hInFacts.left
                                                  (And.intro hOutFacts.right.left
                                                    (And.intro ?_ ?_))))))
                                        · refine (ihqComposeSpec firstDomWidth
                                            firstMidWidth firstCodWidth firstRows
                                            firstRows2 hFirstAll hFirstAll2 _ _).mpr ?_
                                          refine Exists.intro firstMidVec
                                            (And.intro hInFacts.right.right.left ?_)
                                          rw [hMidAligned.left]
                                          exact hOutFacts.right.right.left
                                        · refine (ihqComposeSpec secondDomWidth
                                            secondMidWidth secondCodWidth secondRows
                                            secondRows2 hSecondAll hSecondAll2 _ _).mpr
                                            ?_
                                          refine Exists.intro secondMidVec
                                            (And.intro hInFacts.right.right.right ?_)
                                          rw [hMidAligned.right]
                                          exact hOutFacts.right.right.right
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFirstCompose := (ihqComposeSpec firstDomWidth firstMidWidth
                      firstCodWidth firstRows firstRows2 hFirstAll hFirstAll2
                      firstDomVec firstCodVec).mp hFacts.right.right.left
                    have hSecondCompose := (ihqComposeSpec secondDomWidth secondMidWidth
                      secondCodWidth secondRows secondRows2 hSecondAll hSecondAll2
                      secondDomVec secondCodVec).mp hFacts.right.right.right
                    cases hFirstCompose with
                    | intro firstMidVec hFirstBoth =>
                        cases hSecondCompose with
                        | intro secondMidVec hSecondBoth =>
                            refine Exists.intro (ihqCat firstMidVec secondMidVec)
                              (And.intro ?_ ?_)
                            · refine (ihwTensorSpec firstDomWidth firstMidWidth
                                secondDomWidth secondMidWidth firstRows secondRows
                                hFirstAll hSecondAll _ _).mpr ?_
                              exact Exists.intro firstDomVec (Exists.intro secondDomVec
                                (Exists.intro firstMidVec (Exists.intro secondMidVec
                                  (And.intro hFacts.left (And.intro rfl (And.intro
                                    hFirstBoth.left hSecondBoth.left))))))
                            · refine (ihwTensorSpec firstMidWidth firstCodWidth
                                secondMidWidth secondCodWidth firstRows2 secondRows2
                                hFirstAll2 hSecondAll2 _ _).mpr ?_
                              exact Exists.intro firstMidVec (Exists.intro secondMidVec
                                (Exists.intro firstCodVec (Exists.intro secondCodVec
                                  (And.intro rfl (And.intro hFacts.right.left
                                    (And.intro hFirstBoth.right
                                      hSecondBoth.right))))))

/-! ## Stage 4 — cell-list concatenation, wire layers, the layer split -/

/-- Cons-only concatenation of cell lists. -/
def ihwCatCells : List IhsCell -> List IhsCell -> List IhsCell
  | [], secondCells => secondCells
  | headCell :: restCells, secondCells => headCell :: ihwCatCells restCells secondCells

theorem ihwCatCellsNilRight : (cells : List IhsCell) -> ihwCatCells cells [] = cells
  | [] => rfl
  | headCell :: restCells =>
      congrArg (fun tailCells => headCell :: tailCells) (ihwCatCellsNilRight restCells)

theorem ihwCatCellsDomArity : (firstCells secondCells : List IhsCell) ->
    ihsLayerDomArity (ihwCatCells firstCells secondCells)
      = ihsLayerDomArity firstCells + ihsLayerDomArity secondCells
  | [], secondCells => (Nat.zero_add (ihsLayerDomArity secondCells)).symm
  | headCell :: restCells, secondCells => by
      show ihsCellDomArity headCell
          + ihsLayerDomArity (ihwCatCells restCells secondCells)
        = (ihsCellDomArity headCell + ihsLayerDomArity restCells)
          + ihsLayerDomArity secondCells
      rw [ihwCatCellsDomArity restCells secondCells]
      exact (Nat.add_assoc (ihsCellDomArity headCell) (ihsLayerDomArity restCells)
        (ihsLayerDomArity secondCells)).symm

theorem ihwCatCellsCodArity : (firstCells secondCells : List IhsCell) ->
    ihsLayerCodArity (ihwCatCells firstCells secondCells)
      = ihsLayerCodArity firstCells + ihsLayerCodArity secondCells
  | [], secondCells => (Nat.zero_add (ihsLayerCodArity secondCells)).symm
  | headCell :: restCells, secondCells => by
      show ihsCellCodArity headCell
          + ihsLayerCodArity (ihwCatCells restCells secondCells)
        = (ihsCellCodArity headCell + ihsLayerCodArity restCells)
          + ihsLayerCodArity secondCells
      rw [ihwCatCellsCodArity restCells secondCells]
      exact (Nat.add_assoc (ihsCellCodArity headCell) (ihsLayerCodArity restCells)
        (ihsLayerCodArity secondCells)).symm

/-- The wire layer of a given strand count. -/
def ihwWireCells : Nat -> List IhsCell
  | 0 => []
  | strandPred + 1 => IhsCell.wire :: ihwWireCells strandPred

theorem ihwWireCellsDomArity : (strandCount : Nat) ->
    ihsLayerDomArity (ihwWireCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + ihsLayerDomArity (ihwWireCells strandPred) = strandPred + 1
      rw [ihwWireCellsDomArity strandPred]
      exact Nat.add_comm 1 strandPred

theorem ihwWireCellsCodArity : (strandCount : Nat) ->
    ihsLayerCodArity (ihwWireCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + ihsLayerCodArity (ihwWireCells strandPred) = strandPred + 1
      rw [ihwWireCellsCodArity strandPred]
      exact Nat.add_comm 1 strandPred

/-- The wire layer denotes the identity relation. -/
theorem ihwWireCellsDenoteId : (strandCount : Nat) ->
    IhsRelEquiv strandCount strandCount (ihsLayerDenote (ihwWireCells strandCount))
      (ihqIdRows strandCount)
  | 0 => ihsRelEquivRefl 0 0 []
  | strandPred + 1 => by
      have hInner := ihwWireCellsDenoteId strandPred
      have hStep1 : IhsRelEquiv (1 + strandPred) (1 + strandPred)
          (ihsLayerDenote (ihwWireCells (strandPred + 1)))
          (ihsTensorRows 1 1 strandPred strandPred (ihqIdRows 1)
            (ihqIdRows strandPred)) := by
        show IhsRelEquiv (1 + strandPred) (1 + strandPred)
          (ihsTensorRows 1 1 (ihsLayerDomArity (ihwWireCells strandPred))
            (ihsLayerCodArity (ihwWireCells strandPred)) (ihqIdRows 1)
            (ihsLayerDenote (ihwWireCells strandPred)))
          (ihsTensorRows 1 1 strandPred strandPred (ihqIdRows 1) (ihqIdRows strandPred))
        rw [ihwWireCellsDomArity strandPred, ihwWireCellsCodArity strandPred]
        exact ihwTensorRowsCong 1 1 strandPred strandPred (ihqIdRowsWidth 1)
          (ihqIdRowsWidth 1)
          (ihsAllWidthCast (by rw [ihwWireCellsDomArity strandPred,
            ihwWireCellsCodArity strandPred])
            (ihsLayerDenoteWidth (ihwWireCells strandPred)))
          (ihqIdRowsWidth strandPred) (ihsRelEquivRefl 1 1 (ihqIdRows 1)) hInner
      have hStep2 := ihwTensorIdSum 1 strandPred
      rw [Nat.add_comm 1 strandPred] at hStep1 hStep2
      exact ihsRelEquivTrans hStep1 hStep2

/-- Splitting a layer built by cell concatenation into a tensor of the parts. -/
theorem ihwLayerDenoteCatSplit : (firstCells secondCells : List IhsCell) ->
    IhsRelEquiv (ihsLayerDomArity firstCells + ihsLayerDomArity secondCells)
      (ihsLayerCodArity firstCells + ihsLayerCodArity secondCells)
      (ihsLayerDenote (ihwCatCells firstCells secondCells))
      (ihsTensorRows (ihsLayerDomArity firstCells) (ihsLayerCodArity firstCells)
        (ihsLayerDomArity secondCells) (ihsLayerCodArity secondCells)
        (ihsLayerDenote firstCells) (ihsLayerDenote secondCells))
  | [], secondCells => by
      refine ihsRelEquivCast (Nat.zero_add (ihsLayerDomArity secondCells)).symm
        (Nat.zero_add (ihsLayerCodArity secondCells)).symm ?_
      exact ihsRelEquivSymm (ihwTensorUnitLeft (ihsLayerDomArity secondCells)
        (ihsLayerCodArity secondCells) (ihsLayerDenote secondCells)
        (ihsLayerDenoteWidth secondCells))
  | headCell :: restCells, secondCells => by
      have hInner := ihwLayerDenoteCatSplit restCells secondCells
      have hStep1 : IhsRelEquiv
          (ihsCellDomArity headCell
            + (ihsLayerDomArity restCells + ihsLayerDomArity secondCells))
          (ihsCellCodArity headCell
            + (ihsLayerCodArity restCells + ihsLayerCodArity secondCells))
          (ihsLayerDenote (ihwCatCells (headCell :: restCells) secondCells))
          (ihsTensorRows (ihsCellDomArity headCell) (ihsCellCodArity headCell)
            (ihsLayerDomArity restCells + ihsLayerDomArity secondCells)
            (ihsLayerCodArity restCells + ihsLayerCodArity secondCells)
            (ihsCellRows headCell)
            (ihsTensorRows (ihsLayerDomArity restCells) (ihsLayerCodArity restCells)
              (ihsLayerDomArity secondCells) (ihsLayerCodArity secondCells)
              (ihsLayerDenote restCells) (ihsLayerDenote secondCells))) := by
        show IhsRelEquiv _ _
          (ihsTensorRows (ihsCellDomArity headCell) (ihsCellCodArity headCell)
            (ihsLayerDomArity (ihwCatCells restCells secondCells))
            (ihsLayerCodArity (ihwCatCells restCells secondCells))
            (ihsCellRows headCell) (ihsLayerDenote (ihwCatCells restCells secondCells)))
          _
        rw [ihwCatCellsDomArity restCells secondCells,
          ihwCatCellsCodArity restCells secondCells]
        refine ihwTensorRowsCong (ihsCellDomArity headCell) (ihsCellCodArity headCell)
          (ihsLayerDomArity restCells + ihsLayerDomArity secondCells)
          (ihsLayerCodArity restCells + ihsLayerCodArity secondCells)
          (ihsCellRowsWidth headCell) (ihsCellRowsWidth headCell)
          (ihsAllWidthCast (by rw [ihwCatCellsDomArity restCells secondCells,
            ihwCatCellsCodArity restCells secondCells])
            (ihsLayerDenoteWidth (ihwCatCells restCells secondCells)))
          (ihsTensorRowsWidth (ihsLayerDomArity restCells) (ihsLayerCodArity restCells)
            (ihsLayerDomArity secondCells) (ihsLayerCodArity secondCells)
            (ihsLayerDenote restCells) (ihsLayerDenote secondCells)
            (ihsLayerDenoteWidth restCells) (ihsLayerDenoteWidth secondCells))
          (ihsRelEquivRefl _ _ (ihsCellRows headCell)) hInner
      have hStep2 := ihsRelEquivSymm (ihwTensorRowsAssoc (ihsCellDomArity headCell)
        (ihsCellCodArity headCell) (ihsLayerDomArity restCells)
        (ihsLayerCodArity restCells) (ihsLayerDomArity secondCells)
        (ihsLayerCodArity secondCells) (ihsCellRows headCell) (ihsLayerDenote restCells)
        (ihsLayerDenote secondCells) (ihsCellRowsWidth headCell)
        (ihsLayerDenoteWidth restCells) (ihsLayerDenoteWidth secondCells))
      have hStep1Casted := ihsRelEquivCast
        (Nat.add_assoc (ihsCellDomArity headCell) (ihsLayerDomArity restCells)
          (ihsLayerDomArity secondCells)).symm
        (Nat.add_assoc (ihsCellCodArity headCell) (ihsLayerCodArity restCells)
          (ihsLayerCodArity secondCells)).symm hStep1
      exact ihsRelEquivTrans hStep1Casted hStep2

/-! ## Stage 5 — layer-list concatenation and sequential decomposition -/

/-- Cons-only concatenation of layer lists. -/
def ihwCatLayers : List (List IhsCell) -> List (List IhsCell) -> List (List IhsCell)
  | [], secondLayers => secondLayers
  | headLayer :: restLayers, secondLayers =>
      headLayer :: ihwCatLayers restLayers secondLayers

theorem ihwCatLayersNilRight : (layers : List (List IhsCell)) ->
    ihwCatLayers layers [] = layers
  | [] => rfl
  | headLayer :: restLayers =>
      congrArg (fun tailLayers => headLayer :: tailLayers)
        (ihwCatLayersNilRight restLayers)

theorem ihwLayersCodArityCat : (currentArity : Nat) ->
    (firstLayers secondLayers : List (List IhsCell)) ->
    ihsLayersCodArity currentArity (ihwCatLayers firstLayers secondLayers)
      = ihsLayersCodArity (ihsLayersCodArity currentArity firstLayers) secondLayers
  | _currentArity, [], _secondLayers => rfl
  | _currentArity, layer :: restLayers, secondLayers =>
      ihwLayersCodArityCat (ihsLayerCodArity layer) restLayers secondLayers

theorem ihwLayersWFCat : {currentArity : Nat} ->
    (firstLayers secondLayers : List (List IhsCell)) ->
    IhsLayersWF currentArity firstLayers ->
    IhsLayersWF (ihsLayersCodArity currentArity firstLayers) secondLayers ->
    IhsLayersWF currentArity (ihwCatLayers firstLayers secondLayers)
  | _currentArity, [], _secondLayers, _hFirst, hSecond => hSecond
  | _currentArity, _layer :: restLayers, secondLayers, hFirst, hSecond => by
      cases hFirst with
      | cons hDom hRest =>
          exact IhsLayersWF.cons hDom
            (ihwLayersWFCat restLayers secondLayers hRest hSecond)

/-- Sequential decomposition: the denotation of a concatenated layer list is the
relational composition of the two parts' denotations. -/
theorem ihwLayersDenoteCat : {currentArity : Nat} ->
    (firstLayers secondLayers : List (List IhsCell)) ->
    IhsLayersWF currentArity firstLayers ->
    IhsLayersWF (ihsLayersCodArity currentArity firstLayers) secondLayers ->
    IhsRelEquiv currentArity
      (ihsLayersCodArity (ihsLayersCodArity currentArity firstLayers) secondLayers)
      (ihsLayersDenote currentArity (ihwCatLayers firstLayers secondLayers))
      (ihqComposeRows currentArity (ihsLayersCodArity currentArity firstLayers)
        (ihsLayersCodArity (ihsLayersCodArity currentArity firstLayers) secondLayers)
        (ihsLayersDenote currentArity firstLayers)
        (ihsLayersDenote (ihsLayersCodArity currentArity firstLayers) secondLayers))
  | currentArity, [], secondLayers, _hFirst, hSecond =>
      ihsRelEquivSymm (ihsComposeIdLeft currentArity
        (ihsLayersCodArity currentArity secondLayers)
        (ihsLayersDenote currentArity secondLayers)
        (ihsLayersDenoteWidth secondLayers hSecond))
  | currentArity, layer :: restLayers, secondLayers, hFirst, hSecond => by
      cases hFirst with
      | cons hDom hRest =>
          show IhsRelEquiv currentArity
            (ihsLayersCodArity
              (ihsLayersCodArity (ihsLayerCodArity layer) restLayers) secondLayers)
            (ihqComposeRows currentArity (ihsLayerCodArity layer)
              (ihsLayersCodArity (ihsLayerCodArity layer)
                (ihwCatLayers restLayers secondLayers))
              (ihsLayerDenote layer)
              (ihsLayersDenote (ihsLayerCodArity layer)
                (ihwCatLayers restLayers secondLayers)))
            _
          rw [ihwLayersCodArityCat (ihsLayerCodArity layer) restLayers secondLayers]
          have hLayerAll : IhqAllWidth (currentArity + ihsLayerCodArity layer)
              (ihsLayerDenote layer) :=
            ihsAllWidthCast (by rw [hDom]) (ihsLayerDenoteWidth layer)
          have hRestAll := ihsLayersDenoteWidth restLayers hRest
          have hSecondAll := ihsLayersDenoteWidth secondLayers hSecond
          have hCatAll : IhqAllWidth (ihsLayerCodArity layer
              + ihsLayersCodArity (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
                  secondLayers)
              (ihsLayersDenote (ihsLayerCodArity layer)
                (ihwCatLayers restLayers secondLayers)) :=
            ihsAllWidthCast
              (by rw [ihwLayersCodArityCat (ihsLayerCodArity layer) restLayers
                secondLayers])
              (ihsLayersDenoteWidth (ihwCatLayers restLayers secondLayers)
                (ihwLayersWFCat restLayers secondLayers hRest hSecond))
          have hComposeRestAll := ihqComposeRowsWidth (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            (ihsLayersCodArity (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              secondLayers)
            (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            (ihsLayersDenote (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              secondLayers)
            hRestAll hSecondAll
          have hStep1 := ihsComposeRowsCong currentArity (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              secondLayers)
            hLayerAll hLayerAll hCatAll hComposeRestAll
            (ihsRelEquivRefl currentArity (ihsLayerCodArity layer)
              (ihsLayerDenote layer))
            (ihwLayersDenoteCat restLayers secondLayers hRest hSecond)
          have hStep2 := ihsRelEquivSymm (ihsComposeRowsAssoc currentArity
            (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            (ihsLayersCodArity (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              secondLayers)
            (ihsLayerDenote layer)
            (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            (ihsLayersDenote (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              secondLayers)
            hLayerAll hRestAll hSecondAll)
          exact ihsRelEquivTrans hStep1 hStep2

/-- Snoc commutes with layer-list concatenation into the second part. -/
theorem ihwSnocCatLayers : (firstLayers secondLayers : List (List IhsCell)) ->
    (lastLayer : List IhsCell) ->
    ihsSnocLayers (ihwCatLayers firstLayers secondLayers) lastLayer
      = ihwCatLayers firstLayers (ihsSnocLayers secondLayers lastLayer)
  | [], _secondLayers, _lastLayer => rfl
  | headLayer :: restLayers, secondLayers, lastLayer =>
      congrArg (fun tailLayers => headLayer :: tailLayers)
        (ihwSnocCatLayers restLayers secondLayers lastLayer)

/-! ## Stage 6 — whiskering: identity wires left and right of every layer -/

/-- Whisker one layer with wire cells on both sides. -/
def ihwWhiskerLayer (leftWires rightWires : Nat) (layer : List IhsCell) :
    List IhsCell :=
  ihwCatCells (ihwWireCells leftWires) (ihwCatCells layer (ihwWireCells rightWires))

/-- Whisker every layer of a window. -/
def ihwWhiskerLayers (leftWires rightWires : Nat) :
    List (List IhsCell) -> List (List IhsCell)
  | [] => []
  | layer :: restLayers =>
      ihwWhiskerLayer leftWires rightWires layer
        :: ihwWhiskerLayers leftWires rightWires restLayers

theorem ihwWhiskerLayerDomArity (leftWires rightWires : Nat) (layer : List IhsCell) :
    ihsLayerDomArity (ihwWhiskerLayer leftWires rightWires layer)
      = leftWires + (ihsLayerDomArity layer + rightWires) := by
  show ihsLayerDomArity (ihwCatCells (ihwWireCells leftWires)
      (ihwCatCells layer (ihwWireCells rightWires)))
    = leftWires + (ihsLayerDomArity layer + rightWires)
  rw [ihwCatCellsDomArity, ihwCatCellsDomArity, ihwWireCellsDomArity,
    ihwWireCellsDomArity]

theorem ihwWhiskerLayerCodArity (leftWires rightWires : Nat) (layer : List IhsCell) :
    ihsLayerCodArity (ihwWhiskerLayer leftWires rightWires layer)
      = leftWires + (ihsLayerCodArity layer + rightWires) := by
  show ihsLayerCodArity (ihwCatCells (ihwWireCells leftWires)
      (ihwCatCells layer (ihwWireCells rightWires)))
    = leftWires + (ihsLayerCodArity layer + rightWires)
  rw [ihwCatCellsCodArity, ihwCatCellsCodArity, ihwWireCellsCodArity,
    ihwWireCellsCodArity]

theorem ihwWhiskerLayersCodArity (leftWires rightWires : Nat) :
    (layers : List (List IhsCell)) -> (currentArity : Nat) ->
    ihsLayersCodArity (leftWires + (currentArity + rightWires))
      (ihwWhiskerLayers leftWires rightWires layers)
      = leftWires + (ihsLayersCodArity currentArity layers + rightWires)
  | [], _currentArity => rfl
  | layer :: restLayers, currentArity => by
      show ihsLayersCodArity
          (ihsLayerCodArity (ihwWhiskerLayer leftWires rightWires layer))
          (ihwWhiskerLayers leftWires rightWires restLayers)
        = leftWires + (ihsLayersCodArity (ihsLayerCodArity layer) restLayers
            + rightWires)
      rw [ihwWhiskerLayerCodArity]
      exact ihwWhiskerLayersCodArity leftWires rightWires restLayers
        (ihsLayerCodArity layer)

theorem ihwWhiskerLayersWF (leftWires rightWires : Nat) :
    {currentArity : Nat} -> (layers : List (List IhsCell)) ->
    IhsLayersWF currentArity layers ->
    IhsLayersWF (leftWires + (currentArity + rightWires))
      (ihwWhiskerLayers leftWires rightWires layers)
  | currentArity, [], _hWF =>
      IhsLayersWF.nil (leftWires + (currentArity + rightWires))
  | _currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          refine IhsLayersWF.cons ?_ ?_
          · rw [ihwWhiskerLayerDomArity, hDom]
          · rw [ihwWhiskerLayerCodArity]
            exact ihwWhiskerLayersWF leftWires rightWires restLayers hRest

/-- Whiskering by zero wires on both sides is the identity on layer lists. -/
theorem ihwWhiskerLayersZero : (layers : List (List IhsCell)) ->
    ihwWhiskerLayers 0 0 layers = layers
  | [] => rfl
  | layer :: restLayers => by
      show ihwWhiskerLayer 0 0 layer :: ihwWhiskerLayers 0 0 restLayers
        = layer :: restLayers
      have hLayer : ihwWhiskerLayer 0 0 layer = layer := ihwCatCellsNilRight layer
      rw [hLayer, ihwWhiskerLayersZero restLayers]

/-- One whiskered layer denotes the tensor `id_left (x) (layer (x) id_right)`. -/
theorem ihwWhiskerLayerDenote (leftWires rightWires : Nat) (layer : List IhsCell) :
    IhsRelEquiv (leftWires + (ihsLayerDomArity layer + rightWires))
      (leftWires + (ihsLayerCodArity layer + rightWires))
      (ihsLayerDenote (ihwWhiskerLayer leftWires rightWires layer))
      (ihsTensorRows leftWires leftWires
        (ihsLayerDomArity layer + rightWires) (ihsLayerCodArity layer + rightWires)
        (ihqIdRows leftWires)
        (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
          rightWires rightWires (ihsLayerDenote layer) (ihqIdRows rightWires))) := by
  have hSplitOuter := ihwLayerDenoteCatSplit (ihwWireCells leftWires)
    (ihwCatCells layer (ihwWireCells rightWires))
  rw [ihwWireCellsDomArity, ihwWireCellsCodArity, ihwCatCellsDomArity,
    ihwCatCellsCodArity, ihwWireCellsDomArity, ihwWireCellsCodArity] at hSplitOuter
  have hSplitInner := ihwLayerDenoteCatSplit layer (ihwWireCells rightWires)
  rw [ihwWireCellsDomArity, ihwWireCellsCodArity] at hSplitInner
  have hWireLeftAll : IhqAllWidth (leftWires + leftWires)
      (ihsLayerDenote (ihwWireCells leftWires)) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells leftWires))
  have hWireRightAll : IhqAllWidth (rightWires + rightWires)
      (ihsLayerDenote (ihwWireCells rightWires)) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells rightWires))
  have hInnerCatAll : IhqAllWidth ((ihsLayerDomArity layer + rightWires)
      + (ihsLayerCodArity layer + rightWires))
      (ihsLayerDenote (ihwCatCells layer (ihwWireCells rightWires))) :=
    ihsAllWidthCast (by rw [ihwCatCellsDomArity, ihwCatCellsCodArity,
      ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwCatCells layer (ihwWireCells rightWires)))
  have hInnerTensorAll := ihsTensorRowsWidth (ihsLayerDomArity layer)
    (ihsLayerCodArity layer) rightWires rightWires (ihsLayerDenote layer)
    (ihqIdRows rightWires) (ihsLayerDenoteWidth layer) (ihqIdRowsWidth rightWires)
  have hInnerChain : IhsRelEquiv (ihsLayerDomArity layer + rightWires)
      (ihsLayerCodArity layer + rightWires)
      (ihsLayerDenote (ihwCatCells layer (ihwWireCells rightWires)))
      (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
        rightWires rightWires (ihsLayerDenote layer) (ihqIdRows rightWires)) :=
    ihsRelEquivTrans hSplitInner
      (ihwTensorRowsCong (ihsLayerDomArity layer) (ihsLayerCodArity layer)
        rightWires rightWires (ihsLayerDenoteWidth layer) (ihsLayerDenoteWidth layer)
        hWireRightAll (ihqIdRowsWidth rightWires)
        (ihsRelEquivRefl (ihsLayerDomArity layer) (ihsLayerCodArity layer)
          (ihsLayerDenote layer))
        (ihwWireCellsDenoteId rightWires))
  refine ihsRelEquivTrans hSplitOuter ?_
  exact ihwTensorRowsCong leftWires leftWires (ihsLayerDomArity layer + rightWires)
    (ihsLayerCodArity layer + rightWires)
    hWireLeftAll (ihqIdRowsWidth leftWires) hInnerCatAll hInnerTensorAll
    (ihwWireCellsDenoteId leftWires) hInnerChain

/-- The whiskered window denotes `id_left (x) (window (x) id_right)` — whisker
functoriality by interchange down the layer list. -/
theorem ihwWhiskerLayersDenote (leftWires rightWires : Nat) :
    {currentArity : Nat} -> (layers : List (List IhsCell)) ->
    IhsLayersWF currentArity layers ->
    IhsRelEquiv (leftWires + (currentArity + rightWires))
      (leftWires + (ihsLayersCodArity currentArity layers + rightWires))
      (ihsLayersDenote (leftWires + (currentArity + rightWires))
        (ihwWhiskerLayers leftWires rightWires layers))
      (ihsTensorRows leftWires leftWires (currentArity + rightWires)
        (ihsLayersCodArity currentArity layers + rightWires)
        (ihqIdRows leftWires)
        (ihsTensorRows currentArity (ihsLayersCodArity currentArity layers)
          rightWires rightWires
          (ihsLayersDenote currentArity layers) (ihqIdRows rightWires)))
  | currentArity, [], _hWF => by
      refine ihsRelEquivSymm ?_
      refine ihsRelEquivTrans (ihwTensorRowsCong leftWires leftWires
        (currentArity + rightWires) (currentArity + rightWires)
        (ihqIdRowsWidth leftWires) (ihqIdRowsWidth leftWires)
        (ihsTensorRowsWidth currentArity currentArity rightWires rightWires
          (ihqIdRows currentArity) (ihqIdRows rightWires)
          (ihqIdRowsWidth currentArity) (ihqIdRowsWidth rightWires))
        (ihqIdRowsWidth (currentArity + rightWires))
        (ihsRelEquivRefl leftWires leftWires (ihqIdRows leftWires))
        (ihwTensorIdSum currentArity rightWires)) ?_
      exact ihwTensorIdSum leftWires (currentArity + rightWires)
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          subst hDom
          show IhsRelEquiv
            (leftWires + (ihsLayerDomArity layer + rightWires))
            (leftWires
              + (ihsLayersCodArity (ihsLayerCodArity layer) restLayers + rightWires))
            (ihqComposeRows (leftWires + (ihsLayerDomArity layer + rightWires))
              (ihsLayerCodArity (ihwWhiskerLayer leftWires rightWires layer))
              (ihsLayersCodArity
                (ihsLayerCodArity (ihwWhiskerLayer leftWires rightWires layer))
                (ihwWhiskerLayers leftWires rightWires restLayers))
              (ihsLayerDenote (ihwWhiskerLayer leftWires rightWires layer))
              (ihsLayersDenote
                (ihsLayerCodArity (ihwWhiskerLayer leftWires rightWires layer))
                (ihwWhiskerLayers leftWires rightWires restLayers)))
            _
          rw [ihwWhiskerLayerCodArity leftWires rightWires layer,
            ihwWhiskerLayersCodArity leftWires rightWires restLayers
              (ihsLayerCodArity layer)]
          have hLayerAll := ihsLayerDenoteWidth layer
          have hRestAll := ihsLayersDenoteWidth restLayers hRest
          have hIdLeftAll := ihqIdRowsWidth leftWires
          have hIdRightAll := ihqIdRowsWidth rightWires
          have hWhiskLayerAll : IhqAllWidth
              ((leftWires + (ihsLayerDomArity layer + rightWires))
                + (leftWires + (ihsLayerCodArity layer + rightWires)))
              (ihsLayerDenote (ihwWhiskerLayer leftWires rightWires layer)) :=
            ihsAllWidthCast
              (by rw [ihwWhiskerLayerDomArity, ihwWhiskerLayerCodArity])
              (ihsLayerDenoteWidth (ihwWhiskerLayer leftWires rightWires layer))
          have hWhiskRestAll : IhqAllWidth
              ((leftWires + (ihsLayerCodArity layer + rightWires))
                + (leftWires + (ihsLayersCodArity (ihsLayerCodArity layer) restLayers
                    + rightWires)))
              (ihsLayersDenote (leftWires + (ihsLayerCodArity layer + rightWires))
                (ihwWhiskerLayers leftWires rightWires restLayers)) :=
            ihsAllWidthCast
              (by rw [ihwWhiskerLayersCodArity leftWires rightWires restLayers
                (ihsLayerCodArity layer)])
              (ihsLayersDenoteWidth (ihwWhiskerLayers leftWires rightWires restLayers)
                (ihwWhiskerLayersWF leftWires rightWires restLayers hRest))
          have hInnerTensorInAll := ihsTensorRowsWidth (ihsLayerDomArity layer)
            (ihsLayerCodArity layer) rightWires rightWires (ihsLayerDenote layer)
            (ihqIdRows rightWires) hLayerAll hIdRightAll
          have hInnerTensorOutAll := ihsTensorRowsWidth (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            rightWires rightWires
            (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            (ihqIdRows rightWires) hRestAll hIdRightAll
          have hT1All := ihsTensorRowsWidth leftWires leftWires
            (ihsLayerDomArity layer + rightWires) (ihsLayerCodArity layer + rightWires)
            (ihqIdRows leftWires) _ hIdLeftAll hInnerTensorInAll
          have hT2All := ihsTensorRowsWidth leftWires leftWires
            (ihsLayerCodArity layer + rightWires)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers + rightWires)
            (ihqIdRows leftWires) _ hIdLeftAll hInnerTensorOutAll
          have hStep1 := ihsComposeRowsCong
            (leftWires + (ihsLayerDomArity layer + rightWires))
            (leftWires + (ihsLayerCodArity layer + rightWires))
            (leftWires + (ihsLayersCodArity (ihsLayerCodArity layer) restLayers
              + rightWires))
            hWhiskLayerAll hT1All hWhiskRestAll hT2All
            (ihwWhiskerLayerDenote leftWires rightWires layer)
            (ihwWhiskerLayersDenote leftWires rightWires restLayers hRest)
          have hStep2 := ihwTensorComposeInterchange leftWires leftWires leftWires
            (ihsLayerDomArity layer + rightWires) (ihsLayerCodArity layer + rightWires)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers + rightWires)
            (ihqIdRows leftWires) (ihqIdRows leftWires)
            (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
              rightWires rightWires (ihsLayerDenote layer) (ihqIdRows rightWires))
            (ihsTensorRows (ihsLayerCodArity layer)
              (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              rightWires rightWires
              (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
              (ihqIdRows rightWires))
            hIdLeftAll hIdLeftAll hInnerTensorInAll hInnerTensorOutAll
          have hInnerInter := ihwTensorComposeInterchange (ihsLayerDomArity layer)
            (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            rightWires rightWires rightWires
            (ihsLayerDenote layer) (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            (ihqIdRows rightWires) (ihqIdRows rightWires)
            hLayerAll hRestAll hIdRightAll hIdRightAll
          have hComposeLayerRestAll := ihqComposeRowsWidth (ihsLayerDomArity layer)
            (ihsLayerCodArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            (ihsLayerDenote layer)
            (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
            hLayerAll hRestAll
          have hComposeIdRightAll := ihqComposeRowsWidth rightWires rightWires
            rightWires (ihqIdRows rightWires) (ihqIdRows rightWires)
            hIdRightAll hIdRightAll
          have hInnerFix := ihsRelEquivTrans hInnerInter
            (ihwTensorRowsCong (ihsLayerDomArity layer)
              (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              rightWires rightWires
              hComposeLayerRestAll hComposeLayerRestAll hComposeIdRightAll hIdRightAll
              (ihsRelEquivRefl (ihsLayerDomArity layer)
                (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
                (ihqComposeRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
                  (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
                  (ihsLayerDenote layer)
                  (ihsLayersDenote (ihsLayerCodArity layer) restLayers)))
              (ihsComposeIdLeft rightWires rightWires (ihqIdRows rightWires)
                hIdRightAll))
          have hComposeIdLeftAll := ihqComposeRowsWidth leftWires leftWires leftWires
            (ihqIdRows leftWires) (ihqIdRows leftWires) hIdLeftAll hIdLeftAll
          have hInnerComposeAll := ihqComposeRowsWidth
            (ihsLayerDomArity layer + rightWires) (ihsLayerCodArity layer + rightWires)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers + rightWires)
            (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
              rightWires rightWires (ihsLayerDenote layer) (ihqIdRows rightWires))
            (ihsTensorRows (ihsLayerCodArity layer)
              (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              rightWires rightWires
              (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
              (ihqIdRows rightWires))
            hInnerTensorInAll hInnerTensorOutAll
          have hFinalTensorAll := ihsTensorRowsWidth (ihsLayerDomArity layer)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
            rightWires rightWires
            (ihqComposeRows (ihsLayerDomArity layer) (ihsLayerCodArity layer)
              (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
              (ihsLayerDenote layer)
              (ihsLayersDenote (ihsLayerCodArity layer) restLayers))
            (ihqIdRows rightWires) hComposeLayerRestAll hIdRightAll
          have hStep3 := ihwTensorRowsCong leftWires leftWires
            (ihsLayerDomArity layer + rightWires)
            (ihsLayersCodArity (ihsLayerCodArity layer) restLayers + rightWires)
            hComposeIdLeftAll hIdLeftAll hInnerComposeAll hFinalTensorAll
            (ihsComposeIdLeft leftWires leftWires (ihqIdRows leftWires) hIdLeftAll)
            hInnerFix
          exact ihsRelEquivTrans hStep1 (ihsRelEquivTrans hStep2 hStep3)

/-! ## Stage 7 — the pad combinator -/

/-- Pad a window diagram: whisker every window layer by `leftWires`/`rightWires`
wires and frame the result with context layers before and after. -/
def ihwPadDiagram (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List IhsCell)) (window : IhsDiagram) :
    IhsDiagram :=
  { sourceArity := contextSource
    layers := ihwCatLayers beforeLayers
      (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers)
        afterLayers) }

theorem ihwPadDiagramWF (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List IhsCell)) (window : IhsDiagram)
    (hBeforeWF : IhsLayersWF contextSource beforeLayers)
    (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires))
    (hWindowWF : IhsDiagramWF window)
    (hAfterWF : IhsLayersWF (leftWires + (ihsDiagramCodArity window + rightWires))
      afterLayers) :
    IhsDiagramWF (ihwPadDiagram contextSource leftWires rightWires beforeLayers
      afterLayers window) := by
  show IhsLayersWF contextSource (ihwCatLayers beforeLayers
    (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers))
  refine ihwLayersWFCat beforeLayers
    (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers)
    hBeforeWF ?_
  rw [hBeforeCod]
  refine ihwLayersWFCat (ihwWhiskerLayers leftWires rightWires window.layers)
    afterLayers
    (ihwWhiskerLayersWF leftWires rightWires window.layers hWindowWF) ?_
  rw [ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
  exact hAfterWF

theorem ihwPadDiagramCodArity (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List IhsCell)) (window : IhsDiagram)
    (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires)) :
    ihsDiagramCodArity (ihwPadDiagram contextSource leftWires rightWires beforeLayers
        afterLayers window)
      = ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
          afterLayers := by
  show ihsLayersCodArity contextSource (ihwCatLayers beforeLayers
      (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers))
    = ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
        afterLayers
  rw [ihwLayersCodArityCat, ihwLayersCodArityCat, hBeforeCod,
    ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
  rfl

/-- The padded diagram denotes
`before ; (id_left (x) (window (x) id_right)) ; after`. -/
theorem ihwPadDiagramDenoteDecomp (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List IhsCell)) (window : IhsDiagram)
    (hBeforeWF : IhsLayersWF contextSource beforeLayers)
    (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires))
    (hWindowWF : IhsDiagramWF window)
    (hAfterWF : IhsLayersWF (leftWires + (ihsDiagramCodArity window + rightWires))
      afterLayers) :
    IhsRelEquiv contextSource
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
        afterLayers)
      (ihsDiagramDenote (ihwPadDiagram contextSource leftWires rightWires beforeLayers
        afterLayers window))
      (ihqComposeRows contextSource (leftWires + (window.sourceArity + rightWires))
        (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
          afterLayers)
        (ihsLayersDenote contextSource beforeLayers)
        (ihqComposeRows (leftWires + (window.sourceArity + rightWires))
          (leftWires + (ihsDiagramCodArity window + rightWires))
          (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
            afterLayers)
          (ihsTensorRows leftWires leftWires
            (window.sourceArity + rightWires) (ihsDiagramCodArity window + rightWires)
            (ihqIdRows leftWires)
            (ihsTensorRows window.sourceArity (ihsDiagramCodArity window)
              rightWires rightWires (ihsDiagramDenote window) (ihqIdRows rightWires)))
          (ihsLayersDenote (leftWires + (ihsDiagramCodArity window + rightWires))
            afterLayers))) := by
  have hWhiskerWF := ihwWhiskerLayersWF leftWires rightWires window.layers hWindowWF
  have hMidWF : IhsLayersWF (ihsLayersCodArity contextSource beforeLayers)
      (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers)
        afterLayers) := by
    rw [hBeforeCod]
    refine ihwLayersWFCat (ihwWhiskerLayers leftWires rightWires window.layers)
      afterLayers hWhiskerWF ?_
    rw [ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    exact hAfterWF
  have hOuterCat := ihwLayersDenoteCat beforeLayers
    (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers)
    hBeforeWF hMidWF
  rw [ihwLayersCodArityCat, hBeforeCod,
    ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    at hOuterCat
  have hAfterWFCast : IhsLayersWF
      (ihsLayersCodArity (leftWires + (window.sourceArity + rightWires))
        (ihwWhiskerLayers leftWires rightWires window.layers)) afterLayers := by
    rw [ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    exact hAfterWF
  have hInnerCat := ihwLayersDenoteCat
    (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers hWhiskerWF
    hAfterWFCast
  rw [ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    at hInnerCat
  have hBeforeAll : IhqAllWidth
      (contextSource + (leftWires + (window.sourceArity + rightWires)))
      (ihsLayersDenote contextSource beforeLayers) :=
    ihsAllWidthCast (by rw [hBeforeCod]) (ihsLayersDenoteWidth beforeLayers hBeforeWF)
  have hWhiskerAll : IhqAllWidth
      ((leftWires + (window.sourceArity + rightWires))
        + (leftWires + (ihsDiagramCodArity window + rightWires)))
      (ihsLayersDenote (leftWires + (window.sourceArity + rightWires))
        (ihwWhiskerLayers leftWires rightWires window.layers)) :=
    ihsAllWidthCast (by
      rw [ihwWhiskerLayersCodArity leftWires rightWires window.layers
        window.sourceArity]
      rfl)
      (ihsLayersDenoteWidth (ihwWhiskerLayers leftWires rightWires window.layers)
        hWhiskerWF)
  have hAfterAll := ihsLayersDenoteWidth afterLayers hAfterWF
  have hWindowAll := ihsDiagramDenoteWidth window hWindowWF
  have hInnerTensorAll := ihsTensorRowsWidth window.sourceArity
    (ihsDiagramCodArity window) rightWires rightWires (ihsDiagramDenote window)
    (ihqIdRows rightWires) hWindowAll (ihqIdRowsWidth rightWires)
  have hTensorAll := ihsTensorRowsWidth leftWires leftWires
    (window.sourceArity + rightWires) (ihsDiagramCodArity window + rightWires)
    (ihqIdRows leftWires) _ (ihqIdRowsWidth leftWires) hInnerTensorAll
  have hCatWhiskAfterAll : IhqAllWidth
      ((leftWires + (window.sourceArity + rightWires))
        + ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
            afterLayers)
      (ihsLayersDenote (leftWires + (window.sourceArity + rightWires))
        (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers)
          afterLayers)) := by
    have hRaw := ihsLayersDenoteWidth
      (ihwCatLayers (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers)
      (ihwLayersWFCat (ihwWhiskerLayers leftWires rightWires window.layers) afterLayers
        hWhiskerWF hAfterWFCast)
    refine ihsAllWidthCast ?_ hRaw
    rw [ihwLayersCodArityCat,
      ihwWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    rfl
  have hComposeInner2All := ihqComposeRowsWidth
    (leftWires + (window.sourceArity + rightWires))
    (leftWires + (ihsDiagramCodArity window + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
      afterLayers)
    (ihsTensorRows leftWires leftWires
      (window.sourceArity + rightWires) (ihsDiagramCodArity window + rightWires)
      (ihqIdRows leftWires)
      (ihsTensorRows window.sourceArity (ihsDiagramCodArity window)
        rightWires rightWires (ihsDiagramDenote window) (ihqIdRows rightWires)))
    (ihsLayersDenote (leftWires + (ihsDiagramCodArity window + rightWires)) afterLayers)
    hTensorAll hAfterAll
  refine ihsRelEquivTrans hOuterCat ?_
  refine ihsComposeRowsCong contextSource
    (leftWires + (window.sourceArity + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
      afterLayers)
    hBeforeAll hBeforeAll hCatWhiskAfterAll hComposeInner2All
    (ihsRelEquivRefl contextSource (leftWires + (window.sourceArity + rightWires))
      (ihsLayersDenote contextSource beforeLayers)) ?_
  refine ihsRelEquivTrans hInnerCat ?_
  exact ihsComposeRowsCong (leftWires + (window.sourceArity + rightWires))
    (leftWires + (ihsDiagramCodArity window + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
      afterLayers)
    hWhiskerAll hTensorAll hAfterAll hAfterAll
    (ihwWhiskerLayersDenote leftWires rightWires window.layers hWindowWF)
    (ihsRelEquivRefl (leftWires + (ihsDiagramCodArity window + rightWires))
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity window + rightWires))
        afterLayers)
      (ihsLayersDenote (leftWires + (ihsDiagramCodArity window + rightWires))
        afterLayers))

/-- The identity pad (no wires, no context) is the window itself. -/
theorem ihwPadDiagramIdentityAt (contextSource : Nat) (window : IhsDiagram)
    (hSource : window.sourceArity = contextSource) :
    ihwPadDiagram contextSource 0 0 [] [] window = window := by
  show IhsDiagram.mk contextSource
      (ihwCatLayers (ihwWhiskerLayers 0 0 window.layers) [])
    = window
  rw [ihwWhiskerLayersZero window.layers, ihwCatLayersNilRight window.layers,
    <- hSource]

/-! ## Stage 8 — window moves, the padded step, the whisker congruence (T3) -/

/-- A window move: one committed seed row, or splitting one layer into two
sequential whisker-padded halves (the exchange move, derived sound below). -/
inductive IhwWindowMove : IhsDiagram -> IhsDiagram -> Prop where
  | row (tag : IhsRowTag) : IhwWindowMove (ihsRowLhs tag) (ihsRowRhs tag)
  | splitLayer (leftCells rightCells : List IhsCell) :
      IhwWindowMove
        { sourceArity := ihsLayerDomArity leftCells + ihsLayerDomArity rightCells
          layers := [ihwCatCells leftCells rightCells] }
        { sourceArity := ihsLayerDomArity leftCells + ihsLayerDomArity rightCells
          layers := [ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)),
            ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells] }

/-- Soundness of the layer-split move: the merged layer and its two sequential
halves denote the same relation (THE EXCHANGE DERIVATION, by interchange +
unit collapses). -/
theorem ihwSplitLayerBundle (leftCells rightCells : List IhsCell) :
    IhsConvBundle
      { sourceArity := ihsLayerDomArity leftCells + ihsLayerDomArity rightCells
        layers := [ihwCatCells leftCells rightCells] }
      { sourceArity := ihsLayerDomArity leftCells + ihsLayerDomArity rightCells
        layers := [ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)),
          ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells] } := by
  have hDenLAll := ihsLayerDenoteWidth leftCells
  have hDenRAll := ihsLayerDenoteWidth rightCells
  have hL1DomEq : ihsLayerDomArity
      (ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)))
      = ihsLayerDomArity leftCells + ihsLayerDomArity rightCells := by
    rw [ihwCatCellsDomArity, ihwWireCellsDomArity]
  have hL1CodEq : ihsLayerCodArity
      (ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)))
      = ihsLayerCodArity leftCells + ihsLayerDomArity rightCells := by
    rw [ihwCatCellsCodArity, ihwWireCellsCodArity]
  have hL2DomEq : ihsLayerDomArity
      (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells)
      = ihsLayerCodArity leftCells + ihsLayerDomArity rightCells := by
    rw [ihwCatCellsDomArity, ihwWireCellsDomArity]
  have hL2CodEq : ihsLayerCodArity
      (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells)
      = ihsLayerCodArity leftCells + ihsLayerCodArity rightCells := by
    rw [ihwCatCellsCodArity, ihwWireCellsCodArity]
  have hMergedAll : IhqAllWidth
      ((ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        + ihsLayerCodArity (ihwCatCells leftCells rightCells))
      (ihsLayerDenote (ihwCatCells leftCells rightCells)) :=
    ihsAllWidthCast (by rw [ihwCatCellsDomArity])
      (ihsLayerDenoteWidth (ihwCatCells leftCells rightCells))
  have hL1All : IhqAllWidth
      ((ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        + (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells))
      (ihsLayerDenote (ihwCatCells leftCells
        (ihwWireCells (ihsLayerDomArity rightCells)))) :=
    ihsAllWidthCast (by rw [hL1DomEq, hL1CodEq])
      (ihsLayerDenoteWidth (ihwCatCells leftCells
        (ihwWireCells (ihsLayerDomArity rightCells))))
  have hL2All : IhqAllWidth
      ((ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
        + (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells))
      (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
        rightCells)) :=
    ihsAllWidthCast (by rw [hL2DomEq, hL2CodEq])
      (ihsLayerDenoteWidth (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
        rightCells))
  have hA : IhsRelEquiv (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity (ihwCatCells leftCells rightCells))
      (ihsLayersDenote (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        [ihwCatCells leftCells rightCells])
      (ihsLayerDenote (ihwCatCells leftCells rightCells)) :=
    ihsComposeIdRight (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity (ihwCatCells leftCells rightCells))
      (ihsLayerDenote (ihwCatCells leftCells rightCells)) hMergedAll
  have hW1 : IhsRelEquiv (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      (ihsLayersDenote (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        [ihwCatCells leftCells rightCells])
      (ihsTensorRows (ihsLayerDomArity leftCells) (ihsLayerCodArity leftCells)
        (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
        (ihsLayerDenote leftCells) (ihsLayerDenote rightCells)) :=
    ihsRelEquivTrans
      (ihsRelEquivCast rfl (ihwCatCellsCodArity leftCells rightCells) hA)
      (ihwLayerDenoteCatSplit leftCells rightCells)
  have hCEq : ihsLayersDenote (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      [ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)),
        ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells]
      = ihqComposeRows (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
          (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
          (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
          (ihsLayerDenote (ihwCatCells leftCells
            (ihwWireCells (ihsLayerDomArity rightCells))))
          (ihqComposeRows (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
            (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
            (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
            (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
              rightCells))
            (ihqIdRows (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells))) := by
    show ihqComposeRows (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerCodArity (ihwCatCells leftCells
          (ihwWireCells (ihsLayerDomArity rightCells))))
        (ihsLayerCodArity (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
          rightCells))
        (ihsLayerDenote (ihwCatCells leftCells
          (ihwWireCells (ihsLayerDomArity rightCells))))
        (ihqComposeRows
          (ihsLayerCodArity (ihwCatCells leftCells
            (ihwWireCells (ihsLayerDomArity rightCells))))
          (ihsLayerCodArity (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
            rightCells))
          (ihsLayerCodArity (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
            rightCells))
          (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
            rightCells))
          (ihqIdRows (ihsLayerCodArity (ihwCatCells
            (ihwWireCells (ihsLayerCodArity leftCells)) rightCells))))
      = _
    rw [hL1CodEq, hL2CodEq]
  have hSubA : IhsRelEquiv (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      (ihqComposeRows (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
        (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
        (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
          rightCells))
        (ihqIdRows (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)))
      (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
        rightCells)) :=
    ihsComposeIdRight (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
        rightCells))
      hL2All
  have hCompInnerAll := ihqComposeRowsWidth
    (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
    (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
    (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
    (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
      rightCells))
    (ihqIdRows (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells))
    hL2All (ihqIdRowsWidth (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells))
  have hSubB : IhsRelEquiv (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      (ihsLayersDenote (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        [ihwCatCells leftCells (ihwWireCells (ihsLayerDomArity rightCells)),
          ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells])
      (ihqComposeRows (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
        (ihsLayerDenote (ihwCatCells leftCells
          (ihwWireCells (ihsLayerDomArity rightCells))))
        (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
          rightCells))) := by
    rw [hCEq]
    exact ihsComposeRowsCong (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      hL1All hL1All hCompInnerAll hL2All
      (ihsRelEquivRefl (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
        (ihsLayerDenote (ihwCatCells leftCells
          (ihwWireCells (ihsLayerDomArity rightCells)))))
      hSubA
  have hSplitL1 := ihwLayerDenoteCatSplit leftCells
    (ihwWireCells (ihsLayerDomArity rightCells))
  rw [ihwWireCellsDomArity, ihwWireCellsCodArity] at hSplitL1
  have hSplitL2 := ihwLayerDenoteCatSplit (ihwWireCells (ihsLayerCodArity leftCells))
    rightCells
  rw [ihwWireCellsDomArity, ihwWireCellsCodArity] at hSplitL2
  have hWireDrAll : IhqAllWidth
      (ihsLayerDomArity rightCells + ihsLayerDomArity rightCells)
      (ihsLayerDenote (ihwWireCells (ihsLayerDomArity rightCells))) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells (ihsLayerDomArity rightCells)))
  have hWireClAll : IhqAllWidth
      (ihsLayerCodArity leftCells + ihsLayerCodArity leftCells)
      (ihsLayerDenote (ihwWireCells (ihsLayerCodArity leftCells))) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells (ihsLayerCodArity leftCells)))
  have hFullL1 : IhsRelEquiv
      (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerDenote (ihwCatCells leftCells
        (ihwWireCells (ihsLayerDomArity rightCells))))
      (ihsTensorRows (ihsLayerDomArity leftCells) (ihsLayerCodArity leftCells)
        (ihsLayerDomArity rightCells) (ihsLayerDomArity rightCells)
        (ihsLayerDenote leftCells) (ihqIdRows (ihsLayerDomArity rightCells))) :=
    ihsRelEquivTrans hSplitL1
      (ihwTensorRowsCong (ihsLayerDomArity leftCells) (ihsLayerCodArity leftCells)
        (ihsLayerDomArity rightCells) (ihsLayerDomArity rightCells)
        hDenLAll hDenLAll hWireDrAll (ihqIdRowsWidth (ihsLayerDomArity rightCells))
        (ihsRelEquivRefl (ihsLayerDomArity leftCells) (ihsLayerCodArity leftCells)
          (ihsLayerDenote leftCells))
        (ihwWireCellsDenoteId (ihsLayerDomArity rightCells)))
  have hFullL2 : IhsRelEquiv
      (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
      (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
      (ihsLayerDenote (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
        rightCells))
      (ihsTensorRows (ihsLayerCodArity leftCells) (ihsLayerCodArity leftCells)
        (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
        (ihqIdRows (ihsLayerCodArity leftCells)) (ihsLayerDenote rightCells)) :=
    ihsRelEquivTrans hSplitL2
      (ihwTensorRowsCong (ihsLayerCodArity leftCells) (ihsLayerCodArity leftCells)
        (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
        hWireClAll (ihqIdRowsWidth (ihsLayerCodArity leftCells)) hDenRAll hDenRAll
        (ihwWireCellsDenoteId (ihsLayerCodArity leftCells))
        (ihsRelEquivRefl (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
          (ihsLayerDenote rightCells)))
  have hT1All := ihsTensorRowsWidth (ihsLayerDomArity leftCells)
    (ihsLayerCodArity leftCells) (ihsLayerDomArity rightCells)
    (ihsLayerDomArity rightCells) (ihsLayerDenote leftCells)
    (ihqIdRows (ihsLayerDomArity rightCells)) hDenLAll
    (ihqIdRowsWidth (ihsLayerDomArity rightCells))
  have hT2All := ihsTensorRowsWidth (ihsLayerCodArity leftCells)
    (ihsLayerCodArity leftCells) (ihsLayerDomArity rightCells)
    (ihsLayerCodArity rightCells) (ihqIdRows (ihsLayerCodArity leftCells))
    (ihsLayerDenote rightCells) (ihqIdRowsWidth (ihsLayerCodArity leftCells)) hDenRAll
  have hSubC := ihsComposeRowsCong
    (ihsLayerDomArity leftCells + ihsLayerDomArity rightCells)
    (ihsLayerCodArity leftCells + ihsLayerDomArity rightCells)
    (ihsLayerCodArity leftCells + ihsLayerCodArity rightCells)
    hL1All hT1All hL2All hT2All hFullL1 hFullL2
  have hSubD := ihwTensorComposeInterchange (ihsLayerDomArity leftCells)
    (ihsLayerCodArity leftCells) (ihsLayerCodArity leftCells)
    (ihsLayerDomArity rightCells) (ihsLayerDomArity rightCells)
    (ihsLayerCodArity rightCells)
    (ihsLayerDenote leftCells) (ihqIdRows (ihsLayerCodArity leftCells))
    (ihqIdRows (ihsLayerDomArity rightCells)) (ihsLayerDenote rightCells)
    hDenLAll (ihqIdRowsWidth (ihsLayerCodArity leftCells))
    (ihqIdRowsWidth (ihsLayerDomArity rightCells)) hDenRAll
  have hComposeLIdAll := ihqComposeRowsWidth (ihsLayerDomArity leftCells)
    (ihsLayerCodArity leftCells) (ihsLayerCodArity leftCells)
    (ihsLayerDenote leftCells) (ihqIdRows (ihsLayerCodArity leftCells))
    hDenLAll (ihqIdRowsWidth (ihsLayerCodArity leftCells))
  have hComposeIdRAll := ihqComposeRowsWidth (ihsLayerDomArity rightCells)
    (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
    (ihqIdRows (ihsLayerDomArity rightCells)) (ihsLayerDenote rightCells)
    (ihqIdRowsWidth (ihsLayerDomArity rightCells)) hDenRAll
  have hSubE := ihwTensorRowsCong (ihsLayerDomArity leftCells)
    (ihsLayerCodArity leftCells) (ihsLayerDomArity rightCells)
    (ihsLayerCodArity rightCells)
    hComposeLIdAll hDenLAll hComposeIdRAll hDenRAll
    (ihsComposeIdRight (ihsLayerDomArity leftCells) (ihsLayerCodArity leftCells)
      (ihsLayerDenote leftCells) hDenLAll)
    (ihsComposeIdLeft (ihsLayerDomArity rightCells) (ihsLayerCodArity rightCells)
      (ihsLayerDenote rightCells) hDenRAll)
  have hW2 := ihsRelEquivTrans hSubB
    (ihsRelEquivTrans hSubC (ihsRelEquivTrans hSubD hSubE))
  refine And.intro rfl (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  · show ihsLayerCodArity (ihwCatCells leftCells rightCells)
      = ihsLayersCodArity (ihsLayerCodArity (ihwCatCells leftCells
          (ihwWireCells (ihsLayerDomArity rightCells))))
        [ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells)) rightCells]
    show ihsLayerCodArity (ihwCatCells leftCells rightCells)
      = ihsLayerCodArity (ihwCatCells (ihwWireCells (ihsLayerCodArity leftCells))
          rightCells)
    rw [ihwCatCellsCodArity, hL2CodEq]
  · exact IhsLayersWF.cons (ihwCatCellsDomArity leftCells rightCells)
      (IhsLayersWF.nil (ihsLayerCodArity (ihwCatCells leftCells rightCells)))
  · refine IhsLayersWF.cons hL1DomEq (IhsLayersWF.cons ?_ (IhsLayersWF.nil _))
    rw [hL2DomEq, hL1CodEq]
  · exact ihsRelEquivCast rfl (ihwCatCellsCodArity leftCells rightCells).symm
      (ihsRelEquivTrans hW1 (ihsRelEquivSymm hW2))

/-- Every window move is sound (bundle form). -/
theorem ihwWindowMoveBundle {firstWindow secondWindow : IhsDiagram}
    (hMove : IhwWindowMove firstWindow secondWindow) :
    IhsConvBundle firstWindow secondWindow := by
  cases hMove with
  | row tag => exact ihsRowBundle tag
  | splitLayer leftCells rightCells => exact ihwSplitLayerBundle leftCells rightCells

/-- One whisker rewriting step: a window move fired inside a padding context
(wire whiskering plus before/after context layers, boundary-fit hypotheses
carried by the constructor) — the zxp pad shape. -/
inductive IhwStep : IhsDiagram -> IhsDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List IhsCell))
      {firstWindow secondWindow : IhsDiagram}
      (hMove : IhwWindowMove firstWindow secondWindow)
      (hBeforeWF : IhsLayersWF contextSource beforeLayers)
      (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : IhsLayersWF
        (leftWires + (ihsDiagramCodArity firstWindow + rightWires)) afterLayers) :
      IhwStep
        (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Soundness of one padded step. -/
theorem ihwStepBundle {firstDiagram secondDiagram : IhsDiagram}
    (hStep : IhwStep firstDiagram secondDiagram) :
    IhsConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
    rename_i firstWindow secondWindow
    have hWindowBundle := ihwWindowMoveBundle hMove
    have hSourceEq : firstWindow.sourceArity = secondWindow.sourceArity :=
      hWindowBundle.left
    have hCodEq : ihsDiagramCodArity firstWindow = ihsDiagramCodArity secondWindow :=
      hWindowBundle.right.left
    have hFirstWF : IhsDiagramWF firstWindow := hWindowBundle.right.right.left
    have hSecondWF : IhsDiagramWF secondWindow :=
      hWindowBundle.right.right.right.left
    have hEquiv := hWindowBundle.right.right.right.right
    have hBeforeCod2 : ihsLayersCodArity contextSource beforeLayers
        = leftWires + (secondWindow.sourceArity + rightWires) := by
      rw [hBeforeCod, hSourceEq]
    have hAfterWF2 : IhsLayersWF
        (leftWires + (ihsDiagramCodArity secondWindow + rightWires)) afterLayers := by
      rw [<- hCodEq]
      exact hAfterWF
    have hPadWF1 := ihwPadDiagramWF contextSource leftWires rightWires beforeLayers
      afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
    have hPadWF2 := ihwPadDiagramWF contextSource leftWires rightWires beforeLayers
      afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
    have hDecomp1 := ihwPadDiagramDenoteDecomp contextSource leftWires rightWires
      beforeLayers afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
    have hDecomp2 := ihwPadDiagramDenoteDecomp contextSource leftWires rightWires
      beforeLayers afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
    rw [<- hSourceEq, <- hCodEq] at hDecomp2
    have hBeforeAll : IhqAllWidth
        (contextSource + (leftWires + (firstWindow.sourceArity + rightWires)))
        (ihsLayersDenote contextSource beforeLayers) :=
      ihsAllWidthCast (by rw [hBeforeCod])
        (ihsLayersDenoteWidth beforeLayers hBeforeWF)
    have hAfterAll := ihsLayersDenoteWidth afterLayers hAfterWF
    have hFirstDenAll := ihsDiagramDenoteWidth firstWindow hFirstWF
    have hSecondDenAll : IhqAllWidth
        (firstWindow.sourceArity + ihsDiagramCodArity firstWindow)
        (ihsDiagramDenote secondWindow) :=
      ihsAllWidthCast (by rw [hSourceEq, hCodEq])
        (ihsDiagramDenoteWidth secondWindow hSecondWF)
    have hIdLeftAll := ihqIdRowsWidth leftWires
    have hIdRightAll := ihqIdRowsWidth rightWires
    have hInner1All := ihsTensorRowsWidth firstWindow.sourceArity
      (ihsDiagramCodArity firstWindow) rightWires rightWires
      (ihsDiagramDenote firstWindow) (ihqIdRows rightWires) hFirstDenAll hIdRightAll
    have hInner2All := ihsTensorRowsWidth firstWindow.sourceArity
      (ihsDiagramCodArity firstWindow) rightWires rightWires
      (ihsDiagramDenote secondWindow) (ihqIdRows rightWires) hSecondDenAll hIdRightAll
    have hTensor1All := ihsTensorRowsWidth leftWires leftWires
      (firstWindow.sourceArity + rightWires)
      (ihsDiagramCodArity firstWindow + rightWires) (ihqIdRows leftWires) _
      hIdLeftAll hInner1All
    have hTensor2All := ihsTensorRowsWidth leftWires leftWires
      (firstWindow.sourceArity + rightWires)
      (ihsDiagramCodArity firstWindow + rightWires) (ihqIdRows leftWires) _
      hIdLeftAll hInner2All
    have hMiddle : IhsRelEquiv (leftWires + (firstWindow.sourceArity + rightWires))
        (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        (ihsTensorRows leftWires leftWires
          (firstWindow.sourceArity + rightWires)
          (ihsDiagramCodArity firstWindow + rightWires)
          (ihqIdRows leftWires)
          (ihsTensorRows firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
            rightWires rightWires (ihsDiagramDenote firstWindow)
            (ihqIdRows rightWires)))
        (ihsTensorRows leftWires leftWires
          (firstWindow.sourceArity + rightWires)
          (ihsDiagramCodArity firstWindow + rightWires)
          (ihqIdRows leftWires)
          (ihsTensorRows firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
            rightWires rightWires (ihsDiagramDenote secondWindow)
            (ihqIdRows rightWires))) :=
      ihwTensorRowsCong leftWires leftWires (firstWindow.sourceArity + rightWires)
        (ihsDiagramCodArity firstWindow + rightWires)
        hIdLeftAll hIdLeftAll hInner1All hInner2All
        (ihsRelEquivRefl leftWires leftWires (ihqIdRows leftWires))
        (ihwTensorRowsCong firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
          rightWires rightWires hFirstDenAll hSecondDenAll hIdRightAll hIdRightAll
          hEquiv
          (ihsRelEquivRefl rightWires rightWires (ihqIdRows rightWires)))
    have hCompose1All := ihqComposeRowsWidth
      (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers) _
      (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hTensor1All hAfterAll
    have hCompose2All := ihqComposeRowsWidth
      (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers) _
      (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hTensor2All hAfterAll
    have hMidCong := ihsComposeRowsCong contextSource
      (leftWires + (firstWindow.sourceArity + rightWires))
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hBeforeAll hBeforeAll hCompose1All hCompose2All
      (ihsRelEquivRefl contextSource
        (leftWires + (firstWindow.sourceArity + rightWires))
        (ihsLayersDenote contextSource beforeLayers))
      (ihsComposeRowsCong (leftWires + (firstWindow.sourceArity + rightWires))
        (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
          afterLayers)
        hTensor1All hTensor2All hAfterAll hAfterAll hMiddle
        (ihsRelEquivRefl (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
          (ihsLayersCodArity (leftWires
            + (ihsDiagramCodArity firstWindow + rightWires)) afterLayers)
          (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
            afterLayers)))
    refine And.intro rfl (And.intro ?_ (And.intro hPadWF1 (And.intro hPadWF2 ?_)))
    · rw [ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
        afterLayers firstWindow hBeforeCod,
        ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
          afterLayers secondWindow hBeforeCod2, hCodEq]
    · refine ihsRelEquivCast rfl
        (ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
          afterLayers firstWindow hBeforeCod).symm ?_
      exact ihsRelEquivTrans hDecomp1
        (ihsRelEquivTrans hMidCong (ihsRelEquivSymm hDecomp2))

/-- **THE WHISKER CONGRUENCE**: padded steps (a row or a layer split fired
inside wire whiskering plus context layers), reflexivity on well-formed
diagrams, symmetry, transitivity. -/
inductive IhwConv : IhsDiagram -> IhsDiagram -> Prop where
  | step {firstDiagram secondDiagram : IhsDiagram}
      (hStep : IhwStep firstDiagram secondDiagram) :
      IhwConv firstDiagram secondDiagram
  | refl (diagram : IhsDiagram) (hWF : IhsDiagramWF diagram) : IhwConv diagram diagram
  | symm {firstDiagram secondDiagram : IhsDiagram}
      (hConv : IhwConv firstDiagram secondDiagram) :
      IhwConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : IhsDiagram}
      (hFirst : IhwConv firstDiagram secondDiagram)
      (hSecond : IhwConv secondDiagram thirdDiagram) :
      IhwConv firstDiagram thirdDiagram

/-- **SOUNDNESS of the whisker congruence** (the full seed bundle: boundary
agreement, well-formedness both sides, span equality of the denotations). -/
theorem ihwConvSound {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhwConv firstDiagram secondDiagram) :
    IhsConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact ihwStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (ihsRelEquivRefl diagram.sourceArity (ihsDiagramCodArity diagram)
          (ihsDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact ihsConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact ihsConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE at the whisker level: convertibility forces the
executable span decision to fire `true`. -/
theorem ihwConvSpanEqB {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhwConv firstDiagram secondDiagram) :
    ihqSpanEqB (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)
      = true := by
  have hBundle := ihwConvSound hConv
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

/-- Every committed seed row is one `IhwConv` step on the nose (the identity
pad dissolves). -/
theorem ihwRowConv (tag : IhsRowTag) : IhwConv (ihsRowLhs tag) (ihsRowRhs tag) := by
  have hStep := IhwStep.pad (ihsRowLhs tag).sourceArity 0 0 [] []
    (IhwWindowMove.row tag) (IhsLayersWF.nil (ihsRowLhs tag).sourceArity)
    (Nat.zero_add ((ihsRowLhs tag).sourceArity + 0)).symm
    (IhsLayersWF.nil (0 + (ihsDiagramCodArity (ihsRowLhs tag) + 0)))
  rw [ihwPadDiagramIdentityAt (ihsRowLhs tag).sourceArity (ihsRowLhs tag) rfl,
    ihwPadDiagramIdentityAt (ihsRowLhs tag).sourceArity (ihsRowRhs tag)
      (ihsRowBundle tag).left.symm] at hStep
  exact IhwConv.step hStep

/-! ### The embedding of the committed sequential congruence -/

/-- Prepending a fitting layer preserves whisker convertibility (the context
closure the sequential `prependLayer` constructor needs). -/
theorem ihwConvPrependLayer (newLayer : List IhsCell)
    {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhwConv firstDiagram secondDiagram) :
    ihsLayerCodArity newLayer = firstDiagram.sourceArity ->
    IhwConv
      { sourceArity := ihsLayerDomArity newLayer
        layers := newLayer :: firstDiagram.layers }
      { sourceArity := ihsLayerDomArity newLayer
        layers := newLayer :: secondDiagram.layers } := by
  induction hConv with
  | step hStep =>
      intro hFit
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove
          hBeforeWF hBeforeCod hAfterWF =>
          exact IhwConv.step (IhwStep.pad (ihsLayerDomArity newLayer) leftWires
            rightWires (newLayer :: beforeLayers) afterLayers hMove
            (IhsLayersWF.cons rfl (ihsLayersWFCast hFit.symm hBeforeWF))
            ((congrArg (fun boundaryArity =>
              ihsLayersCodArity boundaryArity beforeLayers) hFit).trans hBeforeCod)
            hAfterWF)
  | refl diagram hWF =>
      intro hFit
      exact IhwConv.refl
        { sourceArity := ihsLayerDomArity newLayer
          layers := newLayer :: diagram.layers }
        (IhsLayersWF.cons rfl (ihsLayersWFCast hFit.symm hWF))
  | symm hInner innerCarried =>
      intro hFit
      exact IhwConv.symm
        (innerCarried (hFit.trans (ihwConvSound hInner).left.symm))
  | trans hFirst _hSecond firstCarried secondCarried =>
      intro hFit
      exact IhwConv.trans (firstCarried hFit)
        (secondCarried (hFit.trans (ihwConvSound hFirst).left))

/-- Appending a fitting layer preserves whisker convertibility (the context
closure the sequential `appendLayer` constructor needs). -/
theorem ihwConvAppendLayer (newLayer : List IhsCell)
    {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhwConv firstDiagram secondDiagram) :
    ihsLayerDomArity newLayer = ihsDiagramCodArity firstDiagram ->
    IhwConv
      { sourceArity := firstDiagram.sourceArity
        layers := ihsSnocLayers firstDiagram.layers newLayer }
      { sourceArity := secondDiagram.sourceArity
        layers := ihsSnocLayers secondDiagram.layers newLayer } := by
  induction hConv with
  | step hStep =>
      intro hFit
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove
          hBeforeWF hBeforeCod hAfterWF =>
          rename_i firstWindow secondWindow
          have hFitAfter : ihsLayerDomArity newLayer
              = ihsLayersCodArity
                  (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
                  afterLayers :=
            hFit.trans (ihwPadDiagramCodArity contextSource leftWires rightWires
              beforeLayers afterLayers firstWindow hBeforeCod)
          have hStepNew := IhwStep.pad contextSource leftWires rightWires beforeLayers
            (ihsSnocLayers afterLayers newLayer) hMove hBeforeWF hBeforeCod
            (ihsLayersWFSnoc afterLayers newLayer hAfterWF hFitAfter)
          have hLayersShape1 : ihsSnocLayers (ihwCatLayers beforeLayers
              (ihwCatLayers (ihwWhiskerLayers leftWires rightWires firstWindow.layers)
                afterLayers)) newLayer
              = ihwCatLayers beforeLayers
                  (ihwCatLayers
                    (ihwWhiskerLayers leftWires rightWires firstWindow.layers)
                    (ihsSnocLayers afterLayers newLayer)) :=
            (ihwSnocCatLayers beforeLayers _ newLayer).trans
              (congrArg (fun tailLayers => ihwCatLayers beforeLayers tailLayers)
                (ihwSnocCatLayers
                  (ihwWhiskerLayers leftWires rightWires firstWindow.layers)
                  afterLayers newLayer))
          have hLayersShape2 : ihsSnocLayers (ihwCatLayers beforeLayers
              (ihwCatLayers (ihwWhiskerLayers leftWires rightWires secondWindow.layers)
                afterLayers)) newLayer
              = ihwCatLayers beforeLayers
                  (ihwCatLayers
                    (ihwWhiskerLayers leftWires rightWires secondWindow.layers)
                    (ihsSnocLayers afterLayers newLayer)) :=
            (ihwSnocCatLayers beforeLayers _ newLayer).trans
              (congrArg (fun tailLayers => ihwCatLayers beforeLayers tailLayers)
                (ihwSnocCatLayers
                  (ihwWhiskerLayers leftWires rightWires secondWindow.layers)
                  afterLayers newLayer))
          show IhwConv
            { sourceArity := contextSource
              layers := ihsSnocLayers (ihwCatLayers beforeLayers
                (ihwCatLayers
                  (ihwWhiskerLayers leftWires rightWires firstWindow.layers)
                  afterLayers)) newLayer }
            { sourceArity := contextSource
              layers := ihsSnocLayers (ihwCatLayers beforeLayers
                (ihwCatLayers
                  (ihwWhiskerLayers leftWires rightWires secondWindow.layers)
                  afterLayers)) newLayer }
          rw [hLayersShape1, hLayersShape2]
          exact IhwConv.step hStepNew
  | refl diagram hWF =>
      intro hFit
      exact IhwConv.refl
        { sourceArity := diagram.sourceArity
          layers := ihsSnocLayers diagram.layers newLayer }
        (ihsLayersWFSnoc diagram.layers newLayer hWF hFit)
  | symm hInner innerCarried =>
      intro hFit
      exact IhwConv.symm
        (innerCarried (hFit.trans (ihwConvSound hInner).right.left.symm))
  | trans hFirst _hSecond firstCarried secondCarried =>
      intro hFit
      exact IhwConv.trans (firstCarried hFit)
        (secondCarried (hFit.trans (ihwConvSound hFirst).right.left))

/-- **THE EMBEDDING**: every derivation of the committed sequential congruence
`IhsConv` is a derivation of the whisker congruence `IhwConv` — rows fire
through the identity pad, the sequential layer congruences through the context
closures. -/
theorem ihwConvOfSeedConv {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhsConv firstDiagram secondDiagram) :
    IhwConv firstDiagram secondDiagram := by
  induction hConv with
  | row tag => exact ihwRowConv tag
  | reflWF diagram hWF => exact IhwConv.refl diagram hWF
  | symm _hInner innerCarried => exact IhwConv.symm innerCarried
  | trans _hFirst _hSecond firstCarried secondCarried =>
      exact IhwConv.trans firstCarried secondCarried
  | prependLayer newLayer hFit _hInner innerCarried =>
      exact ihwConvPrependLayer newLayer innerCarried hFit
  | appendLayer newLayer hFit _hInner innerCarried =>
      exact ihwConvAppendLayer newLayer innerCarried hFit

/-! ## Stage 9 — fires (T4/T5): committed rows INSIDE parallel contexts -/

/-- T4 FIRE (A4 counit in a genuine parallel context): the copy-counit row
fired whiskered by ONE WIRE on each side, under a before-layer that feeds the
right parallel strand through a `scalarBox 2`. -/
theorem ihwFireCounitRowInParallelContext :
    IhwConv
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.wire, IhsCell.blackComult, IhsCell.wire],
          [IhsCell.wire, IhsCell.blackCounit, IhsCell.wire, IhsCell.wire]] }
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.wire, IhsCell.wire, IhsCell.wire]] } :=
  IhwConv.step (IhwStep.pad 3 1 1
    [[IhsCell.wire, IhsCell.wire, IhsCell.scalarBox ihsScalarTwo]] []
    (IhwWindowMove.row IhsRowTag.copyCounit)
    (IhsLayersWF.cons rfl (IhsLayersWF.nil _)) rfl (IhsLayersWF.nil _))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the A4 parallel-context fire. -/
theorem ihwFireCounitRowInParallelContextSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
            [IhsCell.wire, IhsCell.blackComult, IhsCell.wire],
            [IhsCell.wire, IhsCell.blackCounit, IhsCell.wire, IhsCell.wire]] })
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
            [IhsCell.wire, IhsCell.wire, IhsCell.wire]] }) = true := rfl

/-- T4 FIRE (A12 scalar product whiskered right, with an after-layer context):
`2 ; 3 = 6` fired beside a parallel wire, then a discard/wire layer. -/
theorem ihwFireScalarProductRowBesideWire :
    IhwConv
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
          [IhsCell.scalarBox ihsScalarThree, IhsCell.wire],
          [IhsCell.blackCounit, IhsCell.wire]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarSix, IhsCell.wire],
          [IhsCell.blackCounit, IhsCell.wire]] } :=
  IhwConv.step (IhwStep.pad 2 0 1 [] [[IhsCell.blackCounit, IhsCell.wire]]
    (IhwWindowMove.row IhsRowTag.scalarProduct)
    (IhsLayersWF.nil 2) rfl (IhsLayersWF.cons rfl (IhsLayersWF.nil _)))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the A12 parallel-context fire. -/
theorem ihwFireScalarProductRowBesideWireSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
            [IhsCell.scalarBox ihsScalarThree, IhsCell.wire],
            [IhsCell.blackCounit, IhsCell.wire]] })
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarSix, IhsCell.wire],
            [IhsCell.blackCounit, IhsCell.wire]] }) = true := rfl

/-- T4 FIRE (I7 white special whiskered by TWO wires on the left). -/
theorem ihwFireWhiteSpecialRowUnderTwoWires :
    IhwConv
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.wire, IhsCell.whiteComult],
          [IhsCell.wire, IhsCell.wire, IhsCell.whiteMult]] }
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.wire, IhsCell.wire]] } :=
  IhwConv.step (IhwStep.pad 3 2 0 [] []
    (IhwWindowMove.row IhsRowTag.whiteSpecial)
    (IhsLayersWF.nil 3) rfl (IhsLayersWF.nil _))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the I7 whiskered fire. -/
theorem ihwFireWhiteSpecialRowUnderTwoWiresSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.wire, IhsCell.whiteComult],
            [IhsCell.wire, IhsCell.wire, IhsCell.whiteMult]] })
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.wire, IhsCell.wire]] }) = true := rfl

/-- T4 FIRE (A1 add-unit whiskered by one wire on each side). -/
theorem ihwFireAddUnitRowBetweenWires :
    IhwConv
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.whiteUnit, IhsCell.wire, IhsCell.wire],
          [IhsCell.wire, IhsCell.whiteMult, IhsCell.wire]] }
      { sourceArity := 3
        layers := [[IhsCell.wire, IhsCell.wire, IhsCell.wire]] } :=
  IhwConv.step (IhwStep.pad 3 1 1 [] []
    (IhwWindowMove.row IhsRowTag.addUnit)
    (IhsLayersWF.nil 3) rfl (IhsLayersWF.nil _))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the A1 whiskered fire. -/
theorem ihwFireAddUnitRowBetweenWiresSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.whiteUnit, IhsCell.wire, IhsCell.wire],
            [IhsCell.wire, IhsCell.whiteMult, IhsCell.wire]] })
      (ihsDiagramDenote
        { sourceArity := 3
          layers := [[IhsCell.wire, IhsCell.wire, IhsCell.wire]] }) = true := rfl

/-- T5 FIRE (two redexes at PARALLEL positions, fired in sequence): the left
strand's `2;3` collapses to `6` beside the right strand's pending redex, then
the right strand's `2;3` collapses beside the left strand's result. -/
theorem ihwFireTwoScalarRedexesInParallel :
    IhwConv
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
          [IhsCell.scalarBox ihsScalarThree, IhsCell.wire],
          [IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.wire, IhsCell.scalarBox ihsScalarThree]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarSix, IhsCell.wire],
          [IhsCell.wire, IhsCell.scalarBox ihsScalarSix]] } :=
  IhwConv.trans
    (IhwConv.step (IhwStep.pad 2 0 1 []
      [[IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
        [IhsCell.wire, IhsCell.scalarBox ihsScalarThree]]
      (IhwWindowMove.row IhsRowTag.scalarProduct)
      (IhsLayersWF.nil 2) rfl
      (IhsLayersWF.cons rfl (IhsLayersWF.cons rfl (IhsLayersWF.nil _)))))
    (IhwConv.step (IhwStep.pad 2 1 0
      [[IhsCell.scalarBox ihsScalarSix, IhsCell.wire]] []
      (IhwWindowMove.row IhsRowTag.scalarProduct)
      (IhsLayersWF.cons rfl (IhsLayersWF.nil _)) rfl (IhsLayersWF.nil _)))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the two-redex parallel fire. -/
theorem ihwFireTwoScalarRedexesInParallelSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
            [IhsCell.scalarBox ihsScalarThree, IhsCell.wire],
            [IhsCell.wire, IhsCell.scalarBox ihsScalarTwo],
            [IhsCell.wire, IhsCell.scalarBox ihsScalarThree]] })
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarSix, IhsCell.wire],
            [IhsCell.wire, IhsCell.scalarBox ihsScalarSix]] }) = true := rfl

/-- T5 FIRE (the exchange move): a merged two-cell layer splits into its two
sequential whisker-padded halves — the layer-split window move fired through
the identity pad. -/
theorem ihwFireSplitScalarPairLayer :
    IhwConv
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.scalarBox ihsScalarThree]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
          [IhsCell.wire, IhsCell.scalarBox ihsScalarThree]] } :=
  IhwConv.step (IhwStep.pad 2 0 0 [] []
    (IhwWindowMove.splitLayer [IhsCell.scalarBox ihsScalarTwo]
      [IhsCell.scalarBox ihsScalarThree])
    (IhsLayersWF.nil 2) rfl (IhsLayersWF.nil _))

set_option maxHeartbeats 4000000 in
/-- Kernel span pin for the layer-split exchange fire. -/
theorem ihwFireSplitScalarPairLayerSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarTwo,
            IhsCell.scalarBox ihsScalarThree]] })
      (ihsDiagramDenote
        { sourceArity := 2
          layers := [[IhsCell.scalarBox ihsScalarTwo, IhsCell.wire],
            [IhsCell.wire, IhsCell.scalarBox ihsScalarThree]] }) = true := rfl

/-- FALSE CONTROL carried over: the white and black units stay non-convertible
under the WIDER whisker congruence (the seed's kernel `false` pin still
refutes through the new bridge). -/
theorem ihwFireUnitsNotConv :
    Not (IhwConv ihsWhiteUnitDiagram ihsBlackUnitDiagram) :=
  fun hConv =>
    Bool.noConfusion ((ihwConvSpanEqB hConv).symm.trans ihsFireUnitsSpanDistinct)

/-- FALSE CONTROL carried over: scalar 2 and scalar 3 stay non-convertible
under the whisker congruence. -/
theorem ihwFireScalarTwoThreeNotConv :
    Not (IhwConv ihsScalarTwoDiagram ihsScalarThreeDiagram) :=
  fun hConv =>
    Bool.noConfusion
      ((ihwConvSpanEqB hConv).symm.trans ihsFireScalarTwoThreeSpanDistinct)

/-! ## Stage 10 — honesty markers (the NEW-marker supersession pattern) -/

/-- DECIDED: the tensor SPEC (`ihwTensorSpec` — blockwise pair-membership of
`ihsTensorRows`, both directions) is SHIPPED zero-axiom, discharging the tensor
debt recorded by brick 1/2. -/
def ihwHasTensorSpec : Bool := true

/-- DECIDED: the tensor laws — congruence (`ihwTensorRowsCong`), units
(`ihwTensorUnitLeft`/`Right`, `ihwTensorIdSum`), associativity up to span
(`ihwTensorRowsAssoc`), and THE INTERCHANGE (`ihwTensorComposeInterchange`)
at matched boundaries — are SHIPPED zero-axiom. -/
def ihwHasInterchange : Bool := true

/-- DECIDED — SUPERSEDES the committed owner-false `ihsHasWhiskerCongruence`
(which stays byte-intact in the seed per the NEW-marker pattern): the WHISKER
(parallel-context) congruence IS SHIPPED.  `IhwConv` fires any committed seed
row (and the layer-split exchange move) inside a context of left/right
identity wires plus arbitrary well-formed before/after layers (`IhwStep.pad`,
the zxp pad shape), is SOUND with the full seed bundle (`ihwConvSound`), keeps
the refutation bridge (`ihwConvSpanEqB`), and CONTAINS the committed
sequential congruence (`ihwConvOfSeedConv`).

BRICK-4 ROUTE (the arc law; completeness stays owner-false at the seed's
`ihsCompletenessIsProven`): (1) the NORMAL-FORM CENSUS against the BSZ
Section 6 pushout normal form / Theorem 6.4 span-of-matrices factorization —
name the candidate NF carrier (a span pair in Smith-like form), the width
invariants, and the reduction moves realizing it inside `IhwConv`; (2) the
GATE-REFUTATION PASS — machine-refute (kernel `false` pins) every candidate
completeness shortcut that skips the census (in particular: `IhwConv` on
INSTANTIATED scalar rows cannot reach rows at OTHER scalars — the scalar
schema gap of the committed gate is still open at the congruence level);
(3) only THEN the completeness induction over the census. -/
def ihwHasWhiskerCongruence : Bool := true

/-- DECIDED: the committed sequential congruence embeds
(`ihwConvOfSeedConv` — rows through the identity pad, prepend/append through
the context closures `ihwConvPrependLayer`/`ihwConvAppendLayer`). -/
def ihwHasSeedEmbedding : Bool := true

end FX1Poly.ComputerAlgebra
