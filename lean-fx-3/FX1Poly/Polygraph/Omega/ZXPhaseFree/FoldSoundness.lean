import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderTailDeath

/-! # Polygraph/Omega/ZXPhaseFree/FoldSoundness — the generic denotational
soundness of the closed-form fold

The r16 `SpiderTailDeath` solved the tail-death existential in closed form: the
absorbed rows are the fold `zxdFoldRows exitWidth codWidth` of the whiskered-spider
core's own denotation.  The remaining wall was the CONVERSION of the two concrete
diagrams (`zxdZSpiderTailDeathClosedFormConv`), a completeness obligation.  The r16
route note named the completeness-FREE next target: the generic DENOTATIONAL
soundness of the fold — that the whiskered-spider core denotes the SAME span as the
killed core of its closed-form absorbed rows, at ALL configurations, machine-checked
without any completeness reflection.  This round proves exactly that, for both
colours (`zxoFoldSoundnessZ` / `zxoFoldSoundnessX`).

The proof is pure F2 linear algebra over the committed span/denote machinery:

* THE FOLD IS AN F2-LINEAR MAP (`zxoFoldRowZero` / `zxoFoldRowXor`): the fold rewrites
  to `take/drop/cat/xor`, so it preserves the zero row and distributes over `xor`.
  Hence `span (fold M) = fold (span M)` via the committed `zxpMapRowsSpan` bridges.

* THE KILL-CORE PAIR CHARACTERIZATION (`zxoTailPairIff`): the generator-block/kill
  core relates `v` to `w` exactly when `xor v (0^dwidth ++ w)` lies in the span of
  the rows — the `zxnNormalFormDenotes` "rest" structure, extracted with no init.

* THE FOLD/CAT IDENTITY (`zxoFoldCatEq`): `fold (v ++ w) = xor v (0^dwidth ++ w)`,
  so the kill-core condition on the fold rows IS the fold of the pair `v ++ w`.

* THE FOLD REFLECTS SPAN MEMBERSHIP (`zxoFoldReflectsSpan`): given that the fold's
  kernel is contained in `span M`, `x ∈ span M <-> fold x ∈ span (fold M)`.  The
  forward direction is fold-linearity; the backward direction cancels the kernel.

* THE KERNEL IS CONTAINED IN THE SPIDER SPAN (`zxoSpiderZeroBandMemZ` /
  `...X`): the ONLY content.  A kernel vector is `0^exitWidth ++ c ++ c`; as a pair
  `(0^exitWidth ++ c, c)` it lies in the spider-core relation — the cod band `c`
  rides the whisker as identity, the spider fires on the all-zero exit strands, and
  the generator block/kill pass the band untouched (zero generator combination).
  This is the diagonal-shift invariance the whole soundness turns on.

Assembling: `ZxpRelEquiv` between the two cores via `zxoFoldReflectsSpan`, then the
committed `zxpSpanEqBOfRelEquiv`.  Both colours land; five fresh span pins fire and
the content marker `zxoHasFoldSoundness` is true.  Nothing in `SpiderTailDeath`,
`SpiderResidual`, or `AbsorptionInduction` is touched; the conversion wall
(`zxdZSpiderTailDeathClosedFormConvIsProven := false`) stays byte-intact — this
round delivers the SPAN-EQUALITY the conversion would need, not the conversion.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the fold as take/drop/cat and its F2 linearity -/

/-- The split's prefix is `zxpTakeN`. -/
theorem zxoSplitAtFst : (splitCount : Nat) -> (row : List Bool) ->
    (zxdSplitAt splitCount row).fst = zxpTakeN splitCount row
  | 0, _row => rfl
  | _splitPred + 1, [] => rfl
  | splitPred + 1, headBit :: tailBits => by
      show headBit :: (zxdSplitAt splitPred tailBits).fst
        = headBit :: zxpTakeN splitPred tailBits
      rw [zxoSplitAtFst splitPred tailBits]

/-- The split's suffix is `zxpDropN`. -/
theorem zxoSplitAtSnd : (splitCount : Nat) -> (row : List Bool) ->
    (zxdSplitAt splitCount row).snd = zxpDropN splitCount row
  | 0, _row => rfl
  | _splitPred + 1, [] => rfl
  | splitPred + 1, _headBit :: tailBits => by
      show (zxdSplitAt splitPred tailBits).snd = zxpDropN splitPred tailBits
      rw [zxoSplitAtSnd splitPred tailBits]

/-- The fresh row concatenation is `zxpCat`. -/
theorem zxoCatRowEqCat : (firstBits secondBits : List Bool) ->
    zxdCatRow firstBits secondBits = zxpCat firstBits secondBits
  | [], _secondBits => rfl
  | headBit :: tailBits, secondBits => by
      show headBit :: zxdCatRow tailBits secondBits = headBit :: zxpCat tailBits secondBits
      rw [zxoCatRowEqCat tailBits secondBits]

/-- THE FOLD, EXPANDED: keep the first `keepWidth` bits, xor the two `bandWidth`
halves of the remainder — all in `take/drop/cat/xor`. -/
theorem zxoFoldRowExpand (keepWidth bandWidth : Nat) (row : List Bool) :
    zxdFoldRow keepWidth bandWidth row
      = zxpCat (zxpTakeN keepWidth row)
          (zxpRowXor (zxpTakeN bandWidth (zxpDropN keepWidth row))
            (zxpDropN bandWidth (zxpDropN keepWidth row))) := by
  show zxdCatRow (zxdSplitAt keepWidth row).fst
      (zxpRowXor (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).fst
        (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).snd)
    = zxpCat (zxpTakeN keepWidth row)
        (zxpRowXor (zxpTakeN bandWidth (zxpDropN keepWidth row))
          (zxpDropN bandWidth (zxpDropN keepWidth row)))
  rw [zxoSplitAtFst keepWidth row, zxoSplitAtSnd keepWidth row,
    zxoSplitAtFst bandWidth (zxpDropN keepWidth row),
    zxoSplitAtSnd bandWidth (zxpDropN keepWidth row), zxoCatRowEqCat]

/-- The row-fold is the row-map of the single-row fold. -/
theorem zxoFoldRowsEqMapRows (keepWidth bandWidth : Nat) : (rows : List (List Bool)) ->
    zxdFoldRows keepWidth bandWidth rows = zxpMapRows (zxdFoldRow keepWidth bandWidth) rows
  | [] => rfl
  | row :: restRows => by
      show zxdFoldRow keepWidth bandWidth row :: zxdFoldRows keepWidth bandWidth restRows
        = zxdFoldRow keepWidth bandWidth row :: zxpMapRows (zxdFoldRow keepWidth bandWidth) restRows
      rw [zxoFoldRowsEqMapRows keepWidth bandWidth restRows]

/-- A four-way xor rearrangement (swap the two inner operands). -/
theorem zxoXor4Swap (firstRow secondRow thirdRow fourthRow : List Bool) :
    zxpRowXor (zxpRowXor firstRow secondRow) (zxpRowXor thirdRow fourthRow)
      = zxpRowXor (zxpRowXor firstRow thirdRow) (zxpRowXor secondRow fourthRow) := by
  have hInner : zxpRowXor secondRow (zxpRowXor thirdRow fourthRow)
      = zxpRowXor thirdRow (zxpRowXor secondRow fourthRow) := by
    rw [<- zxpRowXorAssoc secondRow thirdRow fourthRow, zxpRowXorComm secondRow thirdRow,
      zxpRowXorAssoc thirdRow secondRow fourthRow]
  rw [zxpRowXorAssoc firstRow secondRow (zxpRowXor thirdRow fourthRow),
    zxpRowXorAssoc firstRow thirdRow (zxpRowXor secondRow fourthRow), hInner]

/-- The fold preserves the zero row. -/
theorem zxoFoldRowZero (keepWidth bandWidth : Nat) :
    zxdFoldRow keepWidth bandWidth (zxpZeroRow ((keepWidth + bandWidth) + bandWidth))
      = zxpZeroRow (keepWidth + bandWidth) := by
  rw [zxoFoldRowExpand, Nat.add_assoc keepWidth bandWidth bandWidth,
    zxpTakeNZeroRowExact keepWidth (bandWidth + bandWidth),
    zxpDropNZeroRowExact keepWidth (bandWidth + bandWidth),
    zxpTakeNZeroRowExact bandWidth bandWidth, zxpDropNZeroRowExact bandWidth bandWidth,
    zxpRowXorZeroRight (zxpZeroRow bandWidth) bandWidth (zxpZeroRowLength bandWidth),
    zxpCatZeroZero keepWidth bandWidth]

/-- The fold distributes over `xor` (F2 linearity). -/
theorem zxoFoldRowXor (keepWidth bandWidth : Nat) (firstRow secondRow : List Bool)
    (hFirst : firstRow.length = (keepWidth + bandWidth) + bandWidth)
    (hSecond : secondRow.length = (keepWidth + bandWidth) + bandWidth) :
    zxdFoldRow keepWidth bandWidth (zxpRowXor firstRow secondRow)
      = zxpRowXor (zxdFoldRow keepWidth bandWidth firstRow)
          (zxdFoldRow keepWidth bandWidth secondRow) := by
  have hFirstAssoc : firstRow.length = keepWidth + (bandWidth + bandWidth) := by
    rw [hFirst, Nat.add_assoc]
  have hSecondAssoc : secondRow.length = keepWidth + (bandWidth + bandWidth) := by
    rw [hSecond, Nat.add_assoc]
  rw [zxoFoldRowExpand keepWidth bandWidth (zxpRowXor firstRow secondRow),
    zxoFoldRowExpand keepWidth bandWidth firstRow, zxoFoldRowExpand keepWidth bandWidth secondRow,
    zxpTakeNXor keepWidth firstRow secondRow, zxpDropNXor keepWidth firstRow secondRow,
    zxpTakeNXor bandWidth (zxpDropN keepWidth firstRow) (zxpDropN keepWidth secondRow),
    zxpDropNXor bandWidth (zxpDropN keepWidth firstRow) (zxpDropN keepWidth secondRow),
    zxpRowXorCat (zxpTakeN keepWidth firstRow)
      (zxpRowXor (zxpTakeN bandWidth (zxpDropN keepWidth firstRow))
        (zxpDropN bandWidth (zxpDropN keepWidth firstRow)))
      (zxpTakeN keepWidth secondRow)
      (zxpRowXor (zxpTakeN bandWidth (zxpDropN keepWidth secondRow))
        (zxpDropN bandWidth (zxpDropN keepWidth secondRow)))
      (by rw [zxpTakeNLength firstRow keepWidth (bandWidth + bandWidth) hFirstAssoc,
        zxpTakeNLength secondRow keepWidth (bandWidth + bandWidth) hSecondAssoc]),
    zxoXor4Swap (zxpTakeN bandWidth (zxpDropN keepWidth firstRow))
      (zxpTakeN bandWidth (zxpDropN keepWidth secondRow))
      (zxpDropN bandWidth (zxpDropN keepWidth firstRow))
      (zxpDropN bandWidth (zxpDropN keepWidth secondRow))]

/-- `0^(a+b) ++ tail = 0^a ++ (0^b ++ tail)`. -/
theorem zxoZeroCatDistrib (firstWidth secondWidth : Nat) (tailRow : List Bool) :
    zxpCat (zxpZeroRow (firstWidth + secondWidth)) tailRow
      = zxpCat (zxpZeroRow firstWidth) (zxpCat (zxpZeroRow secondWidth) tailRow) := by
  rw [<- zxpCatZeroZero firstWidth secondWidth, zxpCatAssoc]

/-- THE FOLD/CAT IDENTITY: folding a pair `v ++ w` xors the cod band `w` into the
input cod band and zeroes the leading `dwidth` boundary strands. -/
theorem zxoFoldCatEq (dwidth cwidth : Nat) (headVec tailVec : List Bool)
    (hHead : headVec.length = dwidth + cwidth) (hTail : tailVec.length = cwidth) :
    zxdFoldRow dwidth cwidth (zxpCat headVec tailVec)
      = zxpRowXor headVec (zxpCat (zxpZeroRow dwidth) tailVec) := by
  have hHeadPrefix : (zxpTakeN dwidth headVec).length = dwidth :=
    zxpTakeNLength headVec dwidth cwidth hHead
  have hHeadSuffix : (zxpDropN dwidth headVec).length = cwidth :=
    zxpDropNLength headVec dwidth cwidth hHead
  have hHeadSplit : zxpCat (zxpTakeN dwidth headVec) (zxpDropN dwidth headVec) = headVec :=
    zxpCatTakeDrop headVec dwidth cwidth hHead
  have hCatForm : zxpCat headVec tailVec
      = zxpCat (zxpTakeN dwidth headVec) (zxpCat (zxpDropN dwidth headVec) tailVec) := by
    rw [<- zxpCatAssoc (zxpTakeN dwidth headVec) (zxpDropN dwidth headVec) tailVec, hHeadSplit]
  have hRhs : zxpRowXor headVec (zxpCat (zxpZeroRow dwidth) tailVec)
      = zxpCat (zxpTakeN dwidth headVec) (zxpRowXor (zxpDropN dwidth headVec) tailVec) := by
    conv => lhs; rw [<- hHeadSplit]
    rw [zxpRowXorCat (zxpTakeN dwidth headVec) (zxpDropN dwidth headVec)
        (zxpZeroRow dwidth) tailVec (by rw [hHeadPrefix, zxpZeroRowLength]),
      zxpRowXorZeroRight (zxpTakeN dwidth headVec) dwidth hHeadPrefix]
  rw [zxoFoldRowExpand dwidth cwidth (zxpCat headVec tailVec), hCatForm,
    zxpTakeNCatExact (zxpTakeN dwidth headVec) (zxpCat (zxpDropN dwidth headVec) tailVec)
      dwidth hHeadPrefix,
    zxpDropNCatExact (zxpTakeN dwidth headVec) (zxpCat (zxpDropN dwidth headVec) tailVec)
      dwidth hHeadPrefix,
    zxpTakeNCatExact (zxpDropN dwidth headVec) tailVec cwidth hHeadSuffix,
    zxpDropNCatExact (zxpDropN dwidth headVec) tailVec cwidth hHeadSuffix, hRhs]

/-- THE FOLD KERNEL FORM: a fold-kernel vector is `0^keepWidth ++ c ++ c`. -/
theorem zxoFoldKerForm (keepWidth bandWidth : Nat) (kerVec : List Bool)
    (hLen : kerVec.length = (keepWidth + bandWidth) + bandWidth)
    (hZero : zxdFoldRow keepWidth bandWidth kerVec = zxpZeroRow (keepWidth + bandWidth)) :
    Exists fun bandVec => bandVec.length = bandWidth
      /\ kerVec = zxpCat (zxpCat (zxpZeroRow keepWidth) bandVec) bandVec := by
  have hLenAssoc : kerVec.length = keepWidth + (bandWidth + bandWidth) := by
    rw [hLen, Nat.add_assoc]
  have hPrefixLen : (zxpTakeN keepWidth kerVec).length = keepWidth :=
    zxpTakeNLength kerVec keepWidth (bandWidth + bandWidth) hLenAssoc
  have hSuffixLen : (zxpDropN keepWidth kerVec).length = bandWidth + bandWidth :=
    zxpDropNLength kerVec keepWidth (bandWidth + bandWidth) hLenAssoc
  rw [zxoFoldRowExpand keepWidth bandWidth kerVec,
    <- zxpCatZeroZero keepWidth bandWidth] at hZero
  have hInj := zxpCatInj (zxpTakeN keepWidth kerVec)
    (zxpRowXor (zxpTakeN bandWidth (zxpDropN keepWidth kerVec))
      (zxpDropN bandWidth (zxpDropN keepWidth kerVec)))
    (zxpZeroRow keepWidth) (zxpZeroRow bandWidth)
    (by rw [hPrefixLen, zxpZeroRowLength]) hZero
  have hFrontLen : (zxpTakeN bandWidth (zxpDropN keepWidth kerVec)).length = bandWidth :=
    zxpTakeNLength (zxpDropN keepWidth kerVec) bandWidth bandWidth hSuffixLen
  have hBackLen : (zxpDropN bandWidth (zxpDropN keepWidth kerVec)).length = bandWidth :=
    zxpDropNLength (zxpDropN keepWidth kerVec) bandWidth bandWidth hSuffixLen
  have hBands : zxpTakeN bandWidth (zxpDropN keepWidth kerVec)
      = zxpDropN bandWidth (zxpDropN keepWidth kerVec) :=
    zxpRowXorEqZeroImpliesEq _ _ bandWidth hFrontLen hBackLen hInj.right
  have hOuterSplit : zxpCat (zxpTakeN keepWidth kerVec) (zxpDropN keepWidth kerVec) = kerVec :=
    zxpCatTakeDrop kerVec keepWidth (bandWidth + bandWidth) hLenAssoc
  have hInnerSplit : zxpCat (zxpTakeN bandWidth (zxpDropN keepWidth kerVec))
      (zxpDropN bandWidth (zxpDropN keepWidth kerVec)) = zxpDropN keepWidth kerVec :=
    zxpCatTakeDrop (zxpDropN keepWidth kerVec) bandWidth bandWidth hSuffixLen
  refine Exists.intro (zxpDropN bandWidth (zxpDropN keepWidth kerVec)) (And.intro hBackLen ?_)
  conv => lhs; rw [<- hOuterSplit]
  rw [hInj.left]
  conv => lhs; rw [<- hInnerSplit]
  rw [hBands, zxpCatAssoc]

/-! ## Stage 1 — the generator-block/kill core pair characterization -/

/-- The generator-block/kill core is well-formed. -/
theorem zxoTailWF (dwidth cwidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (dwidth + cwidth) rows) :
    ZxpLayersWF (dwidth + cwidth)
      (zxpCatLayers (zxnGeneratorBlockLayers rows) [zxnKillLayer dwidth cwidth]) :=
  zxpLayersWFCat _ _ (zxnGeneratorBlockLayersWF rows (dwidth + cwidth) hAll)
    (by rw [zxnGeneratorBlockLayersCodArity rows (dwidth + cwidth) hAll]
        exact ZxpLayersWF.cons (zxnKillLayerDomArity dwidth cwidth) (ZxpLayersWF.nil _))

/-- The generator-block/kill core's codomain arity is `cwidth`. -/
theorem zxoTailCod (dwidth cwidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (dwidth + cwidth) rows) :
    zxpLayersCodArity (dwidth + cwidth)
      (zxpCatLayers (zxnGeneratorBlockLayers rows) [zxnKillLayer dwidth cwidth]) = cwidth := by
  rw [zxpLayersCodArityCat, zxnGeneratorBlockLayersCodArity rows (dwidth + cwidth) hAll]
  exact zxnKillLayerCodArity dwidth cwidth

/-- THE KILL-CORE PAIR CHARACTERIZATION: the generator-block/kill core relates `v`
to `w` exactly when `xor v (0^dwidth ++ w)` lies in the span of the rows. -/
theorem zxoTailPairIff (dwidth cwidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (dwidth + cwidth) rows) (domVec codVec : List Bool) :
    ZxpPairMem (dwidth + cwidth) cwidth
        (zxpLayersDenote (dwidth + cwidth)
          (zxpCatLayers (zxnGeneratorBlockLayers rows) [zxnKillLayer dwidth cwidth]))
        domVec codVec
      <-> (domVec.length = dwidth + cwidth /\ codVec.length = cwidth
            /\ ZxpMemSpan (dwidth + cwidth) rows
                (zxpRowXor domVec (zxpCat (zxpZeroRow dwidth) codVec))) := by
  have hBlocksWF := zxnGeneratorBlockLayersWF rows (dwidth + cwidth) hAll
  have hBlocksCod := zxnGeneratorBlockLayersCodArity rows (dwidth + cwidth) hAll
  have hKillWF : ZxpLayersWF (dwidth + cwidth) [zxnKillLayer dwidth cwidth] :=
    ZxpLayersWF.cons (zxnKillLayerDomArity dwidth cwidth) (ZxpLayersWF.nil _)
  have hKillFinal : zxpLayersCodArity (dwidth + cwidth) [zxnKillLayer dwidth cwidth] = cwidth :=
    zxnKillLayerCodArity dwidth cwidth
  refine Iff.intro ?_ ?_
  · intro hPair
    obtain ⟨midVec, hBlocksPair, hKillPair⟩ :=
      (zxnCatLayersPairIffAt (dwidth + cwidth) (dwidth + cwidth) cwidth
        (zxnGeneratorBlockLayers rows) [zxnKillLayer dwidth cwidth]
        hBlocksWF hBlocksCod hKillWF hKillFinal domVec codVec).mp hPair
    have hBlocks := (zxnGeneratorBlockLayersPairIff rows (dwidth + cwidth) hAll
      domVec midVec).mp hBlocksPair
    have hKill := (zxnKillLayerPairIff dwidth cwidth midVec codVec).mp
      ((zxnSingleLayerPairIffAt (dwidth + cwidth) cwidth (zxnKillLayer dwidth cwidth)
        (zxnKillLayerDomArity dwidth cwidth) (zxnKillLayerCodArity dwidth cwidth)
        midVec codVec).mp hKillPair)
    obtain ⟨hDomLen, _hMidLen, hSpan⟩ := hBlocks
    refine And.intro hDomLen (And.intro hKill.left ?_)
    rw [<- hKill.right]
    exact hSpan
  · intro hPacked
    obtain ⟨hDomLen, hCodLen, hSpan⟩ := hPacked
    refine (zxnCatLayersPairIffAt (dwidth + cwidth) (dwidth + cwidth) cwidth
      (zxnGeneratorBlockLayers rows) [zxnKillLayer dwidth cwidth]
      hBlocksWF hBlocksCod hKillWF hKillFinal domVec codVec).mpr ?_
    refine Exists.intro (zxpCat (zxpZeroRow dwidth) codVec) (And.intro ?_ ?_)
    · refine (zxnGeneratorBlockLayersPairIff rows (dwidth + cwidth) hAll domVec _).mpr ?_
      refine And.intro hDomLen (And.intro ?_ hSpan)
      rw [zxpCatLength, zxpZeroRowLength, hCodLen]
    · refine (zxnSingleLayerPairIffAt (dwidth + cwidth) cwidth (zxnKillLayer dwidth cwidth)
        (zxnKillLayerDomArity dwidth cwidth) (zxnKillLayerCodArity dwidth cwidth)
        (zxpCat (zxpZeroRow dwidth) codVec) codVec).mpr ?_
      exact (zxnKillLayerPairIff dwidth cwidth (zxpCat (zxpZeroRow dwidth) codVec) codVec).mpr
        (And.intro hCodLen rfl)

/-! ## Stage 2 — the fold reflects span membership (given kernel containment) -/

/-- THE FOLD REFLECTS SPAN MEMBERSHIP: when the fold's kernel is contained in the
span of `matrixRows`, `x` lies in that span exactly when `fold x` lies in the span
of the folded rows.  Forward is fold-linearity; backward cancels the kernel. -/
theorem zxoFoldReflectsSpan (keepWidth bandWidth : Nat) (matrixRows : List (List Bool))
    (hAll : ZxpAllWidth ((keepWidth + bandWidth) + bandWidth) matrixRows)
    (hKer : (kerVec : List Bool) -> kerVec.length = (keepWidth + bandWidth) + bandWidth ->
      zxdFoldRow keepWidth bandWidth kerVec = zxpZeroRow (keepWidth + bandWidth) ->
      ZxpMemSpan ((keepWidth + bandWidth) + bandWidth) matrixRows kerVec)
    (baseVec : List Bool) (hBase : baseVec.length = (keepWidth + bandWidth) + bandWidth) :
    ZxpMemSpan ((keepWidth + bandWidth) + bandWidth) matrixRows baseVec
      <-> ZxpMemSpan (keepWidth + bandWidth)
            (zxpMapRows (zxdFoldRow keepWidth bandWidth) matrixRows)
            (zxdFoldRow keepWidth bandWidth baseVec) := by
  refine Iff.intro ?_ ?_
  · intro hMem
    exact zxpMapRowsSpanBwd (zxdFoldRow keepWidth bandWidth) (zxoFoldRowZero keepWidth bandWidth)
      (fun firstRow secondRow hFirst hSecond =>
        zxoFoldRowXor keepWidth bandWidth firstRow secondRow hFirst hSecond) hAll hMem
  · intro hMem
    obtain ⟨sourceVec, hSourceMem, hSourceEq⟩ :=
      zxpMapRowsSpanFwd (zxdFoldRow keepWidth bandWidth) (zxoFoldRowZero keepWidth bandWidth)
        (fun firstRow secondRow hFirst hSecond =>
          zxoFoldRowXor keepWidth bandWidth firstRow secondRow hFirst hSecond) hAll hMem
    have hSourceLen : sourceVec.length = (keepWidth + bandWidth) + bandWidth :=
      zxpMemSpanWidth hAll hSourceMem
    have hFoldSourceLen : (zxdFoldRow keepWidth bandWidth sourceVec).length = keepWidth + bandWidth :=
      zxdFoldRowLength keepWidth bandWidth sourceVec hSourceLen
    have hFoldXorZero : zxdFoldRow keepWidth bandWidth (zxpRowXor baseVec sourceVec)
        = zxpZeroRow (keepWidth + bandWidth) := by
      rw [zxoFoldRowXor keepWidth bandWidth baseVec sourceVec hBase hSourceLen, hSourceEq,
        zxpRowXorSelf, hFoldSourceLen]
    have hXorLen : (zxpRowXor baseVec sourceVec).length = (keepWidth + bandWidth) + bandWidth :=
      zxpRowXorLength baseVec sourceVec ((keepWidth + bandWidth) + bandWidth) hBase hSourceLen
    have hXorMem : ZxpMemSpan ((keepWidth + bandWidth) + bandWidth) matrixRows
        (zxpRowXor baseVec sourceVec) := hKer (zxpRowXor baseVec sourceVec) hXorLen hFoldXorZero
    have hFinalMem : ZxpMemSpan ((keepWidth + bandWidth) + bandWidth) matrixRows
        (zxpRowXor (zxpRowXor baseVec sourceVec) sourceVec) :=
      zxpMemSpanXorClosed hAll hXorMem hSourceMem
    have hReassoc : zxpRowXor (zxpRowXor baseVec sourceVec) sourceVec = baseVec := by
      rw [zxpRowXorAssoc baseVec sourceVec sourceVec, zxpRowXorSelf, hSourceLen,
        zxpRowXorZeroRight baseVec ((keepWidth + bandWidth) + bandWidth) hBase]
    rw [hReassoc] at hFinalMem
    exact hFinalMem

/-! ## Stage 3 — the kernel is contained in the spider-core span (the content) -/

/-- THE Z KERNEL MEMBERSHIP: the diagonal band vector `(0^exitWidth ++ c, c)` lies in
the Z-spider-core relation.  The cod band `c` rides the whisker as identity, the
copy-spider fires on the all-zero exit strands, and the generator block/kill pass
the band through with the zero generator combination. -/
theorem zxoSpiderZeroBandMemZ (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows)
    (bandVec : List Bool) (hBand : bandVec.length = codWidth) :
    ZxpMemSpan (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      (zxpCat (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec) bandVec) := by
  have hLayerDom : zxpLayerDomArity [ZxpCell.zSpider topLegCount botLegCount] = topLegCount := by
    show zxpCellDomArity (ZxpCell.zSpider topLegCount botLegCount) + 0 = topLegCount
    rw [Nat.add_zero]; rfl
  have hLayerCod : zxpLayerCodArity [ZxpCell.zSpider topLegCount botLegCount] = botLegCount := by
    show zxpCellCodArity (ZxpCell.zSpider topLegCount botLegCount) + 0 = botLegCount
    rw [Nat.add_zero]; rfl
  have hHeadDom : zxpLayerDomArity
      (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.zSpider topLegCount botLegCount])
      = (leftWires + (topLegCount + rightWires)) + codWidth := by
    rw [zxpWhiskerLayerDomArity, hLayerDom]
    exact (zxdAssocBridge leftWires topLegCount rightWires codWidth).symm
  have hHeadCod : zxpLayerCodArity
      (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.zSpider topLegCount botLegCount])
      = (leftWires + (botLegCount + rightWires)) + codWidth := by
    rw [zxpWhiskerLayerCodArity, hLayerCod]
    exact (zxdAssocBridge leftWires botLegCount rightWires codWidth).symm
  have hDomForm : zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec
      = zxpCat (zxpZeroRow leftWires)
          (zxpCat (zxpZeroRow topLegCount) (zxpCat (zxpZeroRow rightWires) bandVec)) := by
    rw [zxoZeroCatDistrib leftWires (topLegCount + rightWires) bandVec,
      zxoZeroCatDistrib topLegCount rightWires bandVec]
  have hCodForm : zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec
      = zxpCat (zxpZeroRow leftWires)
          (zxpCat (zxpZeroRow botLegCount) (zxpCat (zxpZeroRow rightWires) bandVec)) := by
    rw [zxoZeroCatDistrib leftWires (botLegCount + rightWires) bandVec,
      zxoZeroCatDistrib botLegCount rightWires bandVec]
  have hCellPair : ZxpPairMem topLegCount botLegCount
      (zxpCellRows (ZxpCell.zSpider topLegCount botLegCount))
      (zxpZeroRow topLegCount) (zxpZeroRow botLegCount) := by
    refine And.intro (zxpZeroRowLength topLegCount)
      (And.intro (zxpZeroRowLength botLegCount) ?_)
    rw [zxpCatZeroZero topLegCount botLegCount]
    exact ZxpMemSpan.zero
  have hWhiskerPair : ZxpPairMem ((leftWires + (topLegCount + rightWires)) + codWidth)
      ((leftWires + (botLegCount + rightWires)) + codWidth)
      (zxpLayerDenote
        (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.zSpider topLegCount botLegCount]))
      (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec)
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) := by
    refine (zxnPadCellPairIffAt leftWires (rightWires + codWidth)
      (ZxpCell.zSpider topLegCount botLegCount)
      ((leftWires + (topLegCount + rightWires)) + codWidth)
      ((leftWires + (botLegCount + rightWires)) + codWidth)
      ((zxdAssocBridge leftWires topLegCount rightWires codWidth).symm)
      ((zxdAssocBridge leftWires botLegCount rightWires codWidth).symm)
      (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec)
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec)).mpr ?_
    exact Exists.intro (zxpZeroRow leftWires) (Exists.intro (zxpZeroRow topLegCount)
      (Exists.intro (zxpCat (zxpZeroRow rightWires) bandVec) (Exists.intro (zxpZeroRow botLegCount)
        (And.intro hDomForm (And.intro hCodForm (And.intro (zxpZeroRowLength leftWires)
          (And.intro (by rw [zxpCatLength, zxpZeroRowLength, hBand]) hCellPair)))))))
  have hTailPair : ZxpPairMem ((leftWires + (botLegCount + rightWires)) + codWidth) codWidth
      (zxpLayersDenote ((leftWires + (botLegCount + rightWires)) + codWidth)
        (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]))
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) bandVec := by
    refine (zxoTailPairIff (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) bandVec).mpr ?_
    refine And.intro (by rw [zxpCatLength, zxpZeroRowLength, hBand]) (And.intro hBand ?_)
    rw [zxpRowXorSelf,
      zxpCatLength (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec,
      zxpZeroRowLength, hBand]
    exact ZxpMemSpan.zero
  have hFull := (zxnConsLayerPairIffAt ((leftWires + (topLegCount + rightWires)) + codWidth)
    ((leftWires + (botLegCount + rightWires)) + codWidth) codWidth
    (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.zSpider topLegCount botLegCount])
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth])
    hHeadDom hHeadCod
    (zxoTailWF (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll)
    (zxoTailCod (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll)
    (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec) bandVec).mpr
    (Exists.intro (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec)
      (And.intro hWhiskerPair hTailPair))
  exact hFull.right.right

/-! ## Stage 4 — the generic fold soundness (both colours) -/

/-- THE Z FOLD SOUNDNESS (completeness-free): the whiskered copy-spider core denotes
the SAME span as the killed core of its closed-form absorbed rows, at every
configuration.  This is the `SpiderTailDeath` route note's tractable target — the
span equality the closed-form conversion would need, machine-checked without any
completeness reflection. -/
theorem zxoFoldSoundnessZ (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    zxpSpanEqB
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      (zxpDiagramDenote
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)))
      = true := by
  have hMWF := zxdSpiderTailCoreZWF topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hMCod := zxdSpiderTailCoreZCod topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hAbsAll := zxdAbsorbedRowsZWidth topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hMAll : ZxpAllWidth
      (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)) := by
    have hWidth := zxpDiagramDenoteWidth
      (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows) hMWF
    rw [hMCod] at hWidth
    exact hWidth
  have hNAll : ZxpAllWidth
      (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))) := by
    have hWidth := zxpLayersDenoteWidth
      (currentArity := (leftWires + (topLegCount + rightWires)) + codWidth)
      (zxpCatLayers
        (zxnGeneratorBlockLayers
          (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
        [zxnKillLayer (leftWires + (topLegCount + rightWires)) codWidth])
      (zxoTailWF (leftWires + (topLegCount + rightWires)) codWidth
        (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
        hAbsAll)
    rw [zxoTailCod (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll] at hWidth
    exact hWidth
  have hAbsEq : zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows
      = zxpMapRows (zxdFoldRow (leftWires + (topLegCount + rightWires)) codWidth)
          (zxpDiagramDenote
            (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)) :=
    zxoFoldRowsEqMapRows (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
  have hKer : (kerVec : List Bool) ->
      kerVec.length = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth ->
      zxdFoldRow (leftWires + (topLegCount + rightWires)) codWidth kerVec
        = zxpZeroRow ((leftWires + (topLegCount + rightWires)) + codWidth) ->
      ZxpMemSpan (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
        (zxpDiagramDenote
          (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
        kerVec := by
    intro kerVec hKerLen hKerZero
    obtain ⟨bandVec, hBand, hKerForm⟩ :=
      zxoFoldKerForm (leftWires + (topLegCount + rightWires)) codWidth kerVec hKerLen hKerZero
    rw [hKerForm]
    exact zxoSpiderZeroBandMemZ topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll bandVec hBand
  refine zxpSpanEqBOfRelEquiv
    (domWidth := (leftWires + (topLegCount + rightWires)) + codWidth) (codWidth := codWidth)
    hMAll hNAll ?_
  intro domVec codVec
  refine Iff.intro (fun hPairM => ?_) (fun hPairN => ?_)
  · obtain ⟨hDomLen, hCodLen, hMemM⟩ := hPairM
    have hCatLen : (zxpCat domVec codVec).length
        = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth := by
      rw [zxpCatLength, hDomLen, hCodLen]
    refine (zxoTailPairIff (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll domVec codVec).mpr (And.intro hDomLen (And.intro hCodLen ?_))
    rw [hAbsEq, <- zxoFoldCatEq (leftWires + (topLegCount + rightWires)) codWidth
      domVec codVec hDomLen hCodLen]
    exact (zxoFoldReflectsSpan (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      hMAll hKer (zxpCat domVec codVec) hCatLen).mp hMemM
  · have hTail := (zxoTailPairIff (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll domVec codVec).mp hPairN
    obtain ⟨hDomLen, hCodLen, hMemAbs⟩ := hTail
    have hCatLen : (zxpCat domVec codVec).length
        = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth := by
      rw [zxpCatLength, hDomLen, hCodLen]
    refine And.intro hDomLen (And.intro hCodLen ?_)
    rw [hAbsEq, <- zxoFoldCatEq (leftWires + (topLegCount + rightWires)) codWidth
      domVec codVec hDomLen hCodLen] at hMemAbs
    exact (zxoFoldReflectsSpan (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      hMAll hKer (zxpCat domVec codVec) hCatLen).mpr hMemAbs

/-- THE X KERNEL MEMBERSHIP (colour mirror): the diagonal band vector rides the
whisker as identity, the parity-spider fires on the all-zero exit strands, and the
generator block/kill pass the band through with the zero generator combination. -/
theorem zxoSpiderZeroBandMemX (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows)
    (bandVec : List Bool) (hBand : bandVec.length = codWidth) :
    ZxpMemSpan (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      (zxpCat (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec) bandVec) := by
  have hLayerDom : zxpLayerDomArity [ZxpCell.xSpider topLegCount botLegCount] = topLegCount := by
    show zxpCellDomArity (ZxpCell.xSpider topLegCount botLegCount) + 0 = topLegCount
    rw [Nat.add_zero]; rfl
  have hLayerCod : zxpLayerCodArity [ZxpCell.xSpider topLegCount botLegCount] = botLegCount := by
    show zxpCellCodArity (ZxpCell.xSpider topLegCount botLegCount) + 0 = botLegCount
    rw [Nat.add_zero]; rfl
  have hHeadDom : zxpLayerDomArity
      (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.xSpider topLegCount botLegCount])
      = (leftWires + (topLegCount + rightWires)) + codWidth := by
    rw [zxpWhiskerLayerDomArity, hLayerDom]
    exact (zxdAssocBridge leftWires topLegCount rightWires codWidth).symm
  have hHeadCod : zxpLayerCodArity
      (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.xSpider topLegCount botLegCount])
      = (leftWires + (botLegCount + rightWires)) + codWidth := by
    rw [zxpWhiskerLayerCodArity, hLayerCod]
    exact (zxdAssocBridge leftWires botLegCount rightWires codWidth).symm
  have hDomForm : zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec
      = zxpCat (zxpZeroRow leftWires)
          (zxpCat (zxpZeroRow topLegCount) (zxpCat (zxpZeroRow rightWires) bandVec)) := by
    rw [zxoZeroCatDistrib leftWires (topLegCount + rightWires) bandVec,
      zxoZeroCatDistrib topLegCount rightWires bandVec]
  have hCodForm : zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec
      = zxpCat (zxpZeroRow leftWires)
          (zxpCat (zxpZeroRow botLegCount) (zxpCat (zxpZeroRow rightWires) bandVec)) := by
    rw [zxoZeroCatDistrib leftWires (botLegCount + rightWires) bandVec,
      zxoZeroCatDistrib botLegCount rightWires bandVec]
  have hCellPair : ZxpPairMem topLegCount botLegCount
      (zxpCellRows (ZxpCell.xSpider topLegCount botLegCount))
      (zxpZeroRow topLegCount) (zxpZeroRow botLegCount) := by
    refine And.intro (zxpZeroRowLength topLegCount)
      (And.intro (zxpZeroRowLength botLegCount) ?_)
    rw [zxpCatZeroZero topLegCount botLegCount]
    exact ZxpMemSpan.zero
  have hWhiskerPair : ZxpPairMem ((leftWires + (topLegCount + rightWires)) + codWidth)
      ((leftWires + (botLegCount + rightWires)) + codWidth)
      (zxpLayerDenote
        (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.xSpider topLegCount botLegCount]))
      (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec)
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) := by
    refine (zxnPadCellPairIffAt leftWires (rightWires + codWidth)
      (ZxpCell.xSpider topLegCount botLegCount)
      ((leftWires + (topLegCount + rightWires)) + codWidth)
      ((leftWires + (botLegCount + rightWires)) + codWidth)
      ((zxdAssocBridge leftWires topLegCount rightWires codWidth).symm)
      ((zxdAssocBridge leftWires botLegCount rightWires codWidth).symm)
      (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec)
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec)).mpr ?_
    exact Exists.intro (zxpZeroRow leftWires) (Exists.intro (zxpZeroRow topLegCount)
      (Exists.intro (zxpCat (zxpZeroRow rightWires) bandVec) (Exists.intro (zxpZeroRow botLegCount)
        (And.intro hDomForm (And.intro hCodForm (And.intro (zxpZeroRowLength leftWires)
          (And.intro (by rw [zxpCatLength, zxpZeroRowLength, hBand]) hCellPair)))))))
  have hTailPair : ZxpPairMem ((leftWires + (botLegCount + rightWires)) + codWidth) codWidth
      (zxpLayersDenote ((leftWires + (botLegCount + rightWires)) + codWidth)
        (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]))
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) bandVec := by
    refine (zxoTailPairIff (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll
      (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec) bandVec).mpr ?_
    refine And.intro (by rw [zxpCatLength, zxpZeroRowLength, hBand]) (And.intro hBand ?_)
    rw [zxpRowXorSelf,
      zxpCatLength (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec,
      zxpZeroRowLength, hBand]
    exact ZxpMemSpan.zero
  have hFull := (zxnConsLayerPairIffAt ((leftWires + (topLegCount + rightWires)) + codWidth)
    ((leftWires + (botLegCount + rightWires)) + codWidth) codWidth
    (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.xSpider topLegCount botLegCount])
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth])
    hHeadDom hHeadCod
    (zxoTailWF (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll)
    (zxoTailCod (leftWires + (botLegCount + rightWires)) codWidth generatorRows hAll)
    (zxpCat (zxpZeroRow (leftWires + (topLegCount + rightWires))) bandVec) bandVec).mpr
    (Exists.intro (zxpCat (zxpZeroRow (leftWires + (botLegCount + rightWires))) bandVec)
      (And.intro hWhiskerPair hTailPair))
  exact hFull.right.right

/-- THE X FOLD SOUNDNESS (completeness-free, colour mirror): the whiskered parity-spider
core denotes the SAME span as the killed core of its closed-form absorbed rows. -/
theorem zxoFoldSoundnessX (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    zxpSpanEqB
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      (zxpDiagramDenote
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)))
      = true := by
  have hMWF := zxdSpiderTailCoreXWF topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hMCod := zxdSpiderTailCoreXCod topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hAbsAll := zxdAbsorbedRowsXWidth topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hMAll : ZxpAllWidth
      (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)) := by
    have hWidth := zxpDiagramDenoteWidth
      (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows) hMWF
    rw [hMCod] at hWidth
    exact hWidth
  have hNAll : ZxpAllWidth
      (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
      (zxpDiagramDenote
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows))) := by
    have hWidth := zxpLayersDenoteWidth
      (currentArity := (leftWires + (topLegCount + rightWires)) + codWidth)
      (zxpCatLayers
        (zxnGeneratorBlockLayers
          (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
        [zxnKillLayer (leftWires + (topLegCount + rightWires)) codWidth])
      (zxoTailWF (leftWires + (topLegCount + rightWires)) codWidth
        (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
        hAbsAll)
    rw [zxoTailCod (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll] at hWidth
    exact hWidth
  have hAbsEq : zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows
      = zxpMapRows (zxdFoldRow (leftWires + (topLegCount + rightWires)) codWidth)
          (zxpDiagramDenote
            (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)) :=
    zxoFoldRowsEqMapRows (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
  have hKer : (kerVec : List Bool) ->
      kerVec.length = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth ->
      zxdFoldRow (leftWires + (topLegCount + rightWires)) codWidth kerVec
        = zxpZeroRow ((leftWires + (topLegCount + rightWires)) + codWidth) ->
      ZxpMemSpan (((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth)
        (zxpDiagramDenote
          (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
        kerVec := by
    intro kerVec hKerLen hKerZero
    obtain ⟨bandVec, hBand, hKerForm⟩ :=
      zxoFoldKerForm (leftWires + (topLegCount + rightWires)) codWidth kerVec hKerLen hKerZero
    rw [hKerForm]
    exact zxoSpiderZeroBandMemX topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll bandVec hBand
  refine zxpSpanEqBOfRelEquiv
    (domWidth := (leftWires + (topLegCount + rightWires)) + codWidth) (codWidth := codWidth)
    hMAll hNAll ?_
  intro domVec codVec
  refine Iff.intro (fun hPairM => ?_) (fun hPairN => ?_)
  · obtain ⟨hDomLen, hCodLen, hMemM⟩ := hPairM
    have hCatLen : (zxpCat domVec codVec).length
        = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth := by
      rw [zxpCatLength, hDomLen, hCodLen]
    refine (zxoTailPairIff (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll domVec codVec).mpr (And.intro hDomLen (And.intro hCodLen ?_))
    rw [hAbsEq, <- zxoFoldCatEq (leftWires + (topLegCount + rightWires)) codWidth
      domVec codVec hDomLen hCodLen]
    exact (zxoFoldReflectsSpan (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      hMAll hKer (zxpCat domVec codVec) hCatLen).mp hMemM
  · have hTail := (zxoTailPairIff (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll domVec codVec).mp hPairN
    obtain ⟨hDomLen, hCodLen, hMemAbs⟩ := hTail
    have hCatLen : (zxpCat domVec codVec).length
        = ((leftWires + (topLegCount + rightWires)) + codWidth) + codWidth := by
      rw [zxpCatLength, hDomLen, hCodLen]
    refine And.intro hDomLen (And.intro hCodLen ?_)
    rw [hAbsEq, <- zxoFoldCatEq (leftWires + (topLegCount + rightWires)) codWidth
      domVec codVec hDomLen hCodLen] at hMemAbs
    exact (zxoFoldReflectsSpan (leftWires + (topLegCount + rightWires)) codWidth
      (zxpDiagramDenote
        (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
      hMAll hKer (zxpCat domVec codVec) hCatLen).mpr hMemAbs

/-! ## Stage 4b — the closed-form conversion reduced to PURE reflection

The generic span equality discharges the ENTIRE span side of the completeness
reflection principle `zxdConvOfSpanReflection`.  With the well-formedness and
boundary side-conditions also discharged mechanically, the whole closed-form
conversion `zxdZSpiderTailDeathClosedFormConv` reduces to EXACTLY `zxdConvOfSpanReflection`
(pure phase-free completeness) — at EVERY configuration, not just the r16 content
instance.  The owner marker `zxdZSpiderTailDeathClosedFormConvIsProven` stays false:
this is a conditional reduction, not an unconditional conversion. -/

/-- Completeness of the structural `Nat` equality gate. -/
theorem zxoNatEqBComplete : (firstValue secondValue : Nat) -> firstValue = secondValue ->
    zxpNatEqB firstValue secondValue = true
  | 0, 0, _hEq => rfl
  | 0, _secondPred + 1, hEq => Nat.noConfusion hEq
  | _firstPred + 1, 0, hEq => Nat.noConfusion hEq
  | firstPred + 1, secondPred + 1, hEq =>
      zxoNatEqBComplete firstPred secondPred (Nat.succ.inj hEq)

/-- A well-formed layer list passes the executable well-formedness gate. -/
theorem zxoLayersWFBOfWF : (currentArity : Nat) -> (layers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity layers -> zxpLayersWFB currentArity layers = true
  | _currentArity, [], _hWF => rfl
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          show cond (zxpNatEqB (zxpLayerDomArity layer) currentArity)
            (zxpLayersWFB (zxpLayerCodArity layer) restLayers) false = true
          rw [zxoNatEqBComplete (zxpLayerDomArity layer) currentArity hDom]
          exact zxoLayersWFBOfWF (zxpLayerCodArity layer) restLayers hRest

/-- A well-formed diagram passes the executable well-formedness gate. -/
theorem zxoDiagramWFBOfWF (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) :
    zxpDiagramWFB diagram = true :=
  zxoLayersWFBOfWF diagram.sourceArity diagram.layers hWF

/-- THE Z CLOSED-FORM CONVERSION FROM PURE REFLECTION: given only the completeness
reflection principle, the whole Z closed-form conversion holds — the span side is
`zxoFoldSoundnessZ`, the well-formedness and boundary sides are mechanical.  This
upgrades the committed content-instance-only `zxdZClosedFormConvOfReflectionAtContentInstance`
to the full generic conversion. -/
theorem zxoZSpiderClosedFormConvOfReflection (hReflection : zxdConvOfSpanReflection) :
    zxdZSpiderTailDeathClosedFormConv := by
  intro topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  have hAbsAll := zxdAbsorbedRowsZWidth topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hCodEq : zxpDiagramCodArity
      (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      = zxpDiagramCodArity
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)) := by
    rw [zxdSpiderTailCoreZCod topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll]
    exact (zxoTailCod (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll).symm
  exact hReflection
    (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdKilledCore topLegCount leftWires rightWires codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))
    (zxoDiagramWFBOfWF _ (zxdSpiderTailCoreZWF topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll))
    (zxoDiagramWFBOfWF _ (zxoTailWF (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll))
    rfl hCodEq
    (zxoFoldSoundnessZ topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll)

/-- THE X CLOSED-FORM CONVERSION FROM PURE REFLECTION (colour mirror). -/
theorem zxoXSpiderClosedFormConvOfReflection (hReflection : zxdConvOfSpanReflection) :
    zxdXSpiderTailDeathClosedFormConv := by
  intro topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  have hAbsAll := zxdAbsorbedRowsXWidth topLegCount botLegCount leftWires rightWires codWidth
    generatorRows hAll
  have hCodEq : zxpDiagramCodArity
      (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      = zxpDiagramCodArity
        (zxdKilledCore topLegCount leftWires rightWires codWidth
          (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)) := by
    rw [zxdSpiderTailCoreXCod topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll]
    exact (zxoTailCod (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll).symm
  exact hReflection
    (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdKilledCore topLegCount leftWires rightWires codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows))
    (zxoDiagramWFBOfWF _ (zxdSpiderTailCoreXWF topLegCount botLegCount leftWires rightWires codWidth
      generatorRows hAll))
    (zxoDiagramWFBOfWF _ (zxoTailWF (leftWires + (topLegCount + rightWires)) codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
      hAbsAll))
    rfl hCodEq
    (zxoFoldSoundnessX topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll)

/-! ## Stage 5 — the generic soundness applied at the committed content instances -/

/-- The Z generic soundness fires at the r16 width-changing content instance
(`botLegCount = 2` down to `topLegCount = 1`), reproducing the committed span pin as
an instance of the GENERIC theorem rather than a bespoke `rfl`. -/
theorem zxoFoldSoundnessZContentFire :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 1 2 0 0 0 [[true, false], [false, true]]))
      (zxpDiagramDenote (zxdKilledCore 1 0 0 0
        (zxdAbsorbedRowsZ 1 2 0 0 0 [[true, false], [false, true]])))
      = true :=
  zxoFoldSoundnessZ 1 2 0 0 0 [[true, false], [false, true]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- The Z generic soundness fires at the joint bands instance (`1 -> 2`, nonzero
left/right/codomain bands, multi-row generator). -/
theorem zxoFoldSoundnessZBandsFire :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 1 2 1 1 1
        [[true, false, false, false, false], [false, true, true, false, false]]))
      (zxpDiagramDenote (zxdKilledCore 1 1 1 1
        (zxdAbsorbedRowsZ 1 2 1 1 1
          [[true, false, false, false, false], [false, true, true, false, false]])))
      = true :=
  zxoFoldSoundnessZ 1 2 1 1 1
    [[true, false, false, false, false], [false, true, true, false, false]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- The Z generic soundness fires at the merge-direction instance (`2 -> 1`). -/
theorem zxoFoldSoundnessZMergeFire :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 2 1 1 0 1 [[true, true, false], [false, false, true]]))
      (zxpDiagramDenote (zxdKilledCore 2 1 0 1
        (zxdAbsorbedRowsZ 2 1 1 0 1 [[true, true, false], [false, false, true]])))
      = true :=
  zxoFoldSoundnessZ 2 1 1 0 1 [[true, true, false], [false, false, true]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- The X generic soundness fires at the r16 X content instance (`1 -> 2`). -/
theorem zxoFoldSoundnessXContentFire :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreX 2 1 0 0 0 [[true]]))
      (zxpDiagramDenote (zxdKilledCore 2 0 0 0
        (zxdAbsorbedRowsX 2 1 0 0 0 [[true]])))
      = true :=
  zxoFoldSoundnessX 2 1 0 0 0 [[true]] (ZxpAllWidth.cons rfl ZxpAllWidth.nil)

/-- The X generic soundness fires at the joint bands instance (`2 -> 1`, nonzero
left/right/codomain bands, multi-row generator). -/
theorem zxoFoldSoundnessXBandsFire :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreX 2 1 1 1 1
        [[true, false, false, false], [false, true, false, true]]))
      (zxpDiagramDenote (zxdKilledCore 2 1 1 1
        (zxdAbsorbedRowsX 2 1 1 1 1
          [[true, false, false, false], [false, true, false, true]])))
      = true :=
  zxoFoldSoundnessX 2 1 1 1 1 [[true, false, false, false], [false, true, false, true]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-! ## Stage 6 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the generic denotational soundness of the closed-form fold
is LIVE for BOTH colours — `zxoFoldSoundnessZ` / `zxoFoldSoundnessX` prove that the
whiskered-spider core denotes the SAME span as the killed core of its closed-form
absorbed rows at EVERY configuration, machine-checked zero-axiom with no completeness
reflection.  The fold's F2-linearity, the kill-core pair characterization, the
fold/cat identity, the fold-reflects-span principle, and the kernel-in-spider-span
content all land; five instance fires reproduce the committed span pins as instances
of the generic theorem. -/
def zxoHasFoldSoundness : Bool := true

/-- CONTENT MARKER (TRUE): the closed-form conversion is REDUCED to pure reflection
for BOTH colours — `zxoZSpiderClosedFormConvOfReflection` /
`zxoXSpiderClosedFormConvOfReflection` prove `zxdConvOfSpanReflection ->
zxdZSpiderTailDeathClosedFormConv` (and the X mirror), discharging the span, the
well-formedness, and the boundary side-conditions GENERICALLY.  The committed owner
marker `zxdZSpiderTailDeathClosedFormConvIsProven` stays false: the conversion is
still conditional on the unproven completeness reflection `zxdConvOfSpanReflection`,
which IS phase-free completeness. -/
def zxoClosedFormConvReducesToReflection : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
