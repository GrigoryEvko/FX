import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerEmbedding

/-! # WalkingMonad — the Δ decision: the Godement/`ofFull` case FINISHES `mapEqOfConv`

`WalkingMonad/MonadWhiskerEmbedding` reduced the soundness leg `mapEqOfConv` to a single owed case: the `ofFull`
(Godement / interchange) constructor of `MonadSaturatedTwoCellConv`.  This file discharges it — the CAP-FREE analog
of the walking-adjunction keystone's block-transpose invariance.  On Δ the walking monad has NO cap and NO counit,
so the two horizontally-independent middle blocks of an interchange redex act on DISJOINT position windows and their
ordinal-sum embeddings COMMUTE (with the width-delta shift built into the shipped `embedLocalMap` region algebra).

## What this file ships (each piece zero-axiom)

  * **`embedLocalMap_mapsInto`** — the ordinal-sum embedding lands in the summed ordinal (region-wise bound).
  * ★ **`monadMonotoneMapOf_hcomp`** — the horizontal composite's map is the two-whisker `composeMap` of the
    ordinal-sum embeddings (`hcomp` is `whiskerRight` then `whiskerLeft`; the vcomp homomorphism + the two whisker
    embeddings assemble it).
  * ★ **`embedLocalMap_disjointCommute`** — the DISJOINT-WINDOW two-block commute: an f-region block (right-context
    varying) and a g-region block (left-context varying) COMMUTE under `composeMap`, the width-delta shift absorbed
    by `embedLocalMap`'s region split.  This is the cap-free heart the orchestrator named.
  * ★ **`monadMonotoneMapOf_interchange`** — the Godement invariance of the fold: `map (hcomp (α⊟α') (β⊟β'))
    = map (vcomp (hcomp α β) (hcomp α' β'))`, via `monadMonotoneMapOf_hcomp` + `embedLocalMap_composeMap` (split the
    inner composites) + `composeMap_middleSwap` (reassociate) + `embedLocalMap_disjointCommute` (the swap itself).
  * ★★ **`monadMonotoneMapOf_mapEqOfConv`** — the COMPLETE soundness leg: `MonadSaturatedTwoCellConv` cells have
    equal monotone maps.  Structural induction: `ofFull` via the interchange invariance + the spine-invariant
    whisker-functoriality cases; the three laws by the seed lemmas; the four congruences by the shipped congruence
    lemmas; refl/symm/trans trivially.  This FINISHES `mapEqOfConv` — the NO-direction of the Δ decision.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (cons-only lists,
pointwise `listExtById`, hand arithmetic, `composeMap_assoc`).  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The ordinal-sum embedding lands in the summed ordinal -/

/-- Weaken a `mapsInto` codomain upward. -/
theorem mapsInto_mono (values : List Nat) (codomain codomain' : Nat) (hle : codomain ≤ codomain')
    (hinto : mapsInto values codomain) : mapsInto values codomain' :=
  fun position hposition => Nat.lt_of_lt_of_le (hinto position hposition) hle

/-- ★ The ordinal-sum embedding `id_L ⊕ localMap ⊕ id_R` of a map into `[midLen]` lands in the summed ordinal
`[leftLen + midLen + rightLen]` — region-wise: the left prefix is `< leftLen`, the shifted middle is
`< leftLen + midLen`, the right suffix is `< leftLen + midLen + rightLen`. -/
theorem embedLocalMap_mapsInto (leftLen midLen rightLen : Nat) (localMap : List Nat)
    (hinto : mapsInto localMap midLen) :
    mapsInto (embedLocalMap leftLen midLen rightLen localMap) (leftLen + midLen + rightLen) := by
  intro position hposition
  rw [embedLocalMap_length] at hposition
  have hpos : position < leftLen + localMap.length + rightLen := hposition
  rcases embedRegionSplit leftLen localMap.length rightLen position hpos with
      hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
  · rw [embedLocalMap_get_left leftLen midLen rightLen localMap position hleft]
    exact Nat.lt_of_lt_of_le hleft
      (Nat.le_trans (Nat.le_add_right leftLen midLen) (Nat.le_add_right (leftLen + midLen) rightLen))
  · rw [embedLocalMap_get_mid leftLen midLen rightLen localMap offset hoff]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (hinto offset hoff) leftLen)
      (Nat.le_add_right (leftLen + midLen) rightLen)
  · rw [embedLocalMap_get_right leftLen midLen rightLen localMap offset hoff]
    exact Nat.add_lt_add_left hoff (leftLen + midLen)

/-! ## The horizontal composite's map is the two-whisker ordinal-sum composite -/

/-- ★ **The map of a horizontal composite.**  `hcomp α β = vcomp (whiskerRight _ α) (whiskerLeft _ β)`, so its map
is the `composeMap` of the two ordinal-sum embeddings — `α` in the f-region with an identity g-suffix, then `β` in
the g-region with an identity f-prefix.  Immediate from the vcomp homomorphism and the two whisker embeddings. -/
theorem monadMonotoneMapOf_hcomp {sourceMode middleMode targetMode : MonadMode}
    {oneCellFDom oneCellFCod : ModalityPath monadGraph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath monadGraph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellGDom oneCellGCod) :
    monadMonotoneMapOf (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = composeMap (embedLocalMap 0 oneCellFCod.length oneCellGDom.length (monadMonotoneMapOf cellAlpha))
          (embedLocalMap oneCellFCod.length oneCellGCod.length 0 (monadMonotoneMapOf cellBeta)) := by
  have hstep := monadMonotoneMapOf_vcomp (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha)
    (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)
  rw [monadMonotoneMapOf_whiskerRight, monadMonotoneMapOf_whiskerLeft] at hstep
  exact hstep

/-! ## The disjoint-window two-block commute -/

/-- ★★ **The DISJOINT-WINDOW commute.**  An f-region block (`mapAU`, whiskered on the right by an identity
`bl`-block) and a g-region block (`mapB`, whiskered on the left by the f-block) act on DISJOINT position windows, so
their ordinal-sum embeddings COMMUTE under `composeMap`.  Running `mapAU` (which grows the f-region to `fh`) then
`mapB` at f-offset `fh` equals running `mapB` (at f-offset `fm = mapAU.length`) then `mapAU` — the width delta
`fh − fm` is exactly the shift the `embedLocalMap` region split absorbs.  Proved pointwise (`listExtById`) by a
two-region case split; the cap-free heart of the Godement invariance (no boundary cap escapes the internal window,
unlike the adjunction). -/
theorem embedLocalMap_disjointCommute (fm fh gm bl : Nat) (mapAU mapB : List Nat)
    (hAUlen : mapAU.length = fm) (hAUinto : mapsInto mapAU fh)
    (hBlen : mapB.length = bl) (hBinto : mapsInto mapB gm) :
    composeMap (embedLocalMap 0 fh bl mapAU) (embedLocalMap fh gm 0 mapB)
      = composeMap (embedLocalMap fm gm 0 mapB) (embedLocalMap 0 fh gm mapAU) := by
  subst hAUlen
  subst hBlen
  apply listExtById
  · rw [composeMap_length, composeMap_length, embedLocalMap_length, embedLocalMap_length,
        Nat.zero_add, Nat.add_zero]
  · intro position hpos
    rw [composeMap_length, embedLocalMap_length, Nat.zero_add] at hpos
    have hposLeft : position < (embedLocalMap 0 fh mapB.length mapAU).length := by
      rw [embedLocalMap_length, Nat.zero_add]; exact hpos
    have hposRight : position < (embedLocalMap mapAU.length gm 0 mapB).length := by
      rw [embedLocalMap_length, Nat.add_zero]; exact hpos
    rw [composeMap_get _ _ position hposLeft, composeMap_get _ _ position hposRight]
    rcases Nat.lt_or_ge position mapAU.length with hf | hf
    · -- f-region: position < mapAU.length
      have hL1 : monotoneMapGet (embedLocalMap 0 fh mapB.length mapAU) position
          = monotoneMapGet mapAU position := by
        have h := embedLocalMap_get_mid 0 fh mapB.length mapAU position hf
        rw [Nat.zero_add, Nat.zero_add] at h; exact h
      have hR1 : monotoneMapGet (embedLocalMap mapAU.length gm 0 mapB) position = position :=
        embedLocalMap_get_left mapAU.length gm 0 mapB position hf
      rw [hL1, hR1]
      have hL2 : monotoneMapGet (embedLocalMap fh gm 0 mapB) (monotoneMapGet mapAU position)
          = monotoneMapGet mapAU position :=
        embedLocalMap_get_left fh gm 0 mapB (monotoneMapGet mapAU position) (hAUinto position hf)
      have hR2 : monotoneMapGet (embedLocalMap 0 fh gm mapAU) position = monotoneMapGet mapAU position := by
        have h := embedLocalMap_get_mid 0 fh gm mapAU position hf
        rw [Nat.zero_add, Nat.zero_add] at h; exact h
      rw [hL2, hR2]
    · -- g-region: position = mapAU.length + offset, offset < mapB.length
      obtain ⟨offset, rfl⟩ := Nat.le.dest hf
      have hoff : offset < mapB.length := Nat.lt_of_add_lt_add_left hpos
      have hL1 : monotoneMapGet (embedLocalMap 0 fh mapB.length mapAU) (mapAU.length + offset)
          = fh + offset := by
        have h := embedLocalMap_get_right 0 fh mapB.length mapAU offset hoff
        rw [Nat.zero_add, Nat.zero_add] at h; exact h
      have hR1 : monotoneMapGet (embedLocalMap mapAU.length gm 0 mapB) (mapAU.length + offset)
          = mapAU.length + monotoneMapGet mapB offset :=
        embedLocalMap_get_mid mapAU.length gm 0 mapB offset hoff
      rw [hL1, hR1]
      have hL2 : monotoneMapGet (embedLocalMap fh gm 0 mapB) (fh + offset)
          = fh + monotoneMapGet mapB offset :=
        embedLocalMap_get_mid fh gm 0 mapB offset hoff
      have hR2 : monotoneMapGet (embedLocalMap 0 fh gm mapAU) (mapAU.length + monotoneMapGet mapB offset)
          = fh + monotoneMapGet mapB offset := by
        have h := embedLocalMap_get_right 0 fh gm mapAU (monotoneMapGet mapB offset) (hBinto offset hoff)
        rw [Nat.zero_add, Nat.zero_add] at h; exact h
      rw [hL2, hR2]

/-! ## The middle-swap reassociation -/

/-- Reassociate a four-block `composeMap` product so that the middle two blocks may be swapped: given the swap
`B ∘ C = C' ∘ B'` on the middle blocks (in range), the whole products agree.  Pure `composeMap_assoc`
bookkeeping. -/
theorem composeMap_middleSwap (mapA mapB mapC mapD mapC' mapB' : List Nat)
    (hAB : mapsInto mapA mapB.length) (hBC : mapsInto mapB mapC.length)
    (hAC' : mapsInto mapA mapC'.length) (hC'B' : mapsInto mapC' mapB'.length)
    (hswap : composeMap mapB mapC = composeMap mapC' mapB') :
    composeMap (composeMap mapA mapB) (composeMap mapC mapD)
      = composeMap (composeMap mapA mapC') (composeMap mapB' mapD) := by
  rw [composeMap_assoc mapA mapB (composeMap mapC mapD) hAB,
      ← composeMap_assoc mapB mapC mapD hBC, hswap,
      composeMap_assoc mapC' mapB' mapD hC'B',
      ← composeMap_assoc mapA mapC' (composeMap mapB' mapD) hAC']

/-! ## The Godement invariance of the fold -/

/-- ★★ **The Godement / interchange invariance of the monotone fold.**  The two orders of the Godement product
fold to the SAME monotone map: `map (hcomp (α ⊟ α') (β ⊟ β')) = map (vcomp (hcomp α β) (hcomp α' β'))`.  Assembled
from `monadMonotoneMapOf_hcomp` (both sides become two-whisker composites), `embedLocalMap_composeMap` (split the
inner vcomps of the redex), `composeMap_middleSwap` (reassociate to expose the middle blocks), and
`embedLocalMap_disjointCommute` (the middle blocks — α' in the f-region, β in the g-region — COMMUTE, cap-free on
Δ).  This is the `ofFull` residual, discharged. -/
theorem monadMonotoneMapOf_interchange {sourceMode middleMode targetMode : MonadMode}
    {fLow fMid fHigh : ModalityPath monadGraph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath monadGraph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr monadModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr monadModeSignature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr monadModeSignature gMid gHigh) :
    monadMonotoneMapOf (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
      = monadMonotoneMapOf (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)) := by
  have hrange1 : mapsInto (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellAlphaUpper).length := by
    rw [monadMonotoneMapOf_length cellAlphaUpper]; exact monadMonotoneMapOf_mapsInto cellAlpha
  have hrange2 : mapsInto (monadMonotoneMapOf cellBeta) (monadMonotoneMapOf cellBetaUpper).length := by
    rw [monadMonotoneMapOf_length cellBetaUpper]; exact monadMonotoneMapOf_mapsInto cellBeta
  -- The four blocks (A shared, D shared, B/C swap with C'/B').
  have hAB : mapsInto (embedLocalMap 0 fMid.length gLow.length (monadMonotoneMapOf cellAlpha))
      (embedLocalMap 0 fHigh.length gLow.length (monadMonotoneMapOf cellAlphaUpper)).length := by
    rw [embedLocalMap_length, monadMonotoneMapOf_length cellAlphaUpper]
    exact embedLocalMap_mapsInto 0 fMid.length gLow.length _ (monadMonotoneMapOf_mapsInto cellAlpha)
  have hBinto : mapsInto (embedLocalMap 0 fHigh.length gLow.length (monadMonotoneMapOf cellAlphaUpper))
      (fHigh.length + gLow.length) := by
    have hb := embedLocalMap_mapsInto 0 fHigh.length gLow.length _ (monadMonotoneMapOf_mapsInto cellAlphaUpper)
    rw [Nat.zero_add] at hb; exact hb
  have hClen : (embedLocalMap fHigh.length gMid.length 0 (monadMonotoneMapOf cellBeta)).length
      = fHigh.length + gLow.length := by
    rw [embedLocalMap_length, monadMonotoneMapOf_length cellBeta]; exact Nat.add_zero _
  have hBC : mapsInto (embedLocalMap 0 fHigh.length gLow.length (monadMonotoneMapOf cellAlphaUpper))
      (embedLocalMap fHigh.length gMid.length 0 (monadMonotoneMapOf cellBeta)).length := by
    rw [hClen]; exact hBinto
  have hAinto : mapsInto (embedLocalMap 0 fMid.length gLow.length (monadMonotoneMapOf cellAlpha))
      (fMid.length + gLow.length) := by
    have ha := embedLocalMap_mapsInto 0 fMid.length gLow.length _ (monadMonotoneMapOf_mapsInto cellAlpha)
    rw [Nat.zero_add] at ha; exact ha
  have hC'len : (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta)).length
      = fMid.length + gLow.length := by
    rw [embedLocalMap_length, monadMonotoneMapOf_length cellBeta]; exact Nat.add_zero _
  have hAC' : mapsInto (embedLocalMap 0 fMid.length gLow.length (monadMonotoneMapOf cellAlpha))
      (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta)).length := by
    rw [hC'len]; exact hAinto
  have hC'into : mapsInto (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta))
      (fMid.length + gMid.length) := by
    have hc := embedLocalMap_mapsInto fMid.length gMid.length 0 _ (monadMonotoneMapOf_mapsInto cellBeta)
    rw [Nat.add_zero] at hc; exact hc
  have hB'len : (embedLocalMap 0 fHigh.length gMid.length (monadMonotoneMapOf cellAlphaUpper)).length
      = fMid.length + gMid.length := by
    rw [embedLocalMap_length, monadMonotoneMapOf_length cellAlphaUpper]
    exact congrArg (· + gMid.length) (Nat.zero_add fMid.length)
  have hC'B' : mapsInto (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta))
      (embedLocalMap 0 fHigh.length gMid.length (monadMonotoneMapOf cellAlphaUpper)).length := by
    rw [hB'len]; exact hC'into
  have hswap : composeMap (embedLocalMap 0 fHigh.length gLow.length (monadMonotoneMapOf cellAlphaUpper))
        (embedLocalMap fHigh.length gMid.length 0 (monadMonotoneMapOf cellBeta))
      = composeMap (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta))
        (embedLocalMap 0 fHigh.length gMid.length (monadMonotoneMapOf cellAlphaUpper)) :=
    embedLocalMap_disjointCommute fMid.length fHigh.length gMid.length gLow.length
      (monadMonotoneMapOf cellAlphaUpper) (monadMonotoneMapOf cellBeta)
      (monadMonotoneMapOf_length cellAlphaUpper) (monadMonotoneMapOf_mapsInto cellAlphaUpper)
      (monadMonotoneMapOf_length cellBeta) (monadMonotoneMapOf_mapsInto cellBeta)
  rw [monadMonotoneMapOf_hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper),
      monadMonotoneMapOf_vcomp cellAlpha cellAlphaUpper, monadMonotoneMapOf_vcomp cellBeta cellBetaUpper,
      embedLocalMap_composeMap 0 gLow.length fHigh.length (monadMonotoneMapOf cellAlpha)
        (monadMonotoneMapOf cellAlphaUpper) hrange1,
      embedLocalMap_composeMap fHigh.length 0 gHigh.length (monadMonotoneMapOf cellBeta)
        (monadMonotoneMapOf cellBetaUpper) hrange2,
      monadMonotoneMapOf_length cellAlphaUpper, monadMonotoneMapOf_length cellBetaUpper,
      monadMonotoneMapOf_vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper),
      monadMonotoneMapOf_hcomp cellAlpha cellBeta, monadMonotoneMapOf_hcomp cellAlphaUpper cellBetaUpper]
  exact composeMap_middleSwap
    (embedLocalMap 0 fMid.length gLow.length (monadMonotoneMapOf cellAlpha))
    (embedLocalMap 0 fHigh.length gLow.length (monadMonotoneMapOf cellAlphaUpper))
    (embedLocalMap fHigh.length gMid.length 0 (monadMonotoneMapOf cellBeta))
    (embedLocalMap fHigh.length gHigh.length 0 (monadMonotoneMapOf cellBetaUpper))
    (embedLocalMap fMid.length gMid.length 0 (monadMonotoneMapOf cellBeta))
    (embedLocalMap 0 fHigh.length gMid.length (monadMonotoneMapOf cellAlphaUpper))
    hAB hBC hAC' hC'B' hswap

/-! ## The `ofFull` case and the complete `mapEqOfConv` -/

/-- A `TwoCellStep` (Godement `interchange` INCLUDED) preserves the monotone map.  The eleven structural laws are
spine-invariant (`monadMonotoneMapOf_congr_of_spine_eq rfl`), the four congruences use the shipped congruence
lemmas, and `interchange` is `monadMonotoneMapOf_interchange`. -/
theorem monadMonotoneMapOf_eqOfStep {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (step : TwoCellStep monadModeSignature cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  induction step with
  | vcompIdLeft _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | vcompIdRight _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | vcompAssoc _ _ _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerLeftId _ _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightId _ _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerLeftVcomp _ _ _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightVcomp _ _ _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | vcompCongrLeft cellBeta _ ih => exact monadMonotoneMapOf_vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact monadMonotoneMapOf_vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerRightCongr oneCell ih
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      exact monadMonotoneMapOf_interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper

/-- The free `TwoCellConv` preserves the monotone map (single step / refl / symm / trans). -/
theorem monadMonotoneMapOf_eqOfConv {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : TwoCellConv monadModeSignature cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  induction conv with
  | ofStep step => exact monadMonotoneMapOf_eqOfStep step
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ The COMPLETED `TwoCellConvFull` preserves the monotone map: `ofConv` via `monadMonotoneMapOf_eqOfConv`; the
five whisker-functoriality laws relate SAME-SPINE cells (`castBoundary` is spine-invisible, the whisker shifts are
`composePath` identities), discharged by `monadMonotoneMapOf_congr_of_spine_eq`; the four congruences by the shipped
congruence lemmas; refl/symm/trans trivially. -/
theorem monadMonotoneMapOf_eqOfConvFull {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull monadModeSignature cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  induction convFull with
  | ofConv conv => exact monadMonotoneMapOf_eqOfConv conv
  | whiskerLeftUnit _ => exact monadMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightUnit _ => exact monadMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | whiskerLeftComp _ _ _ => exact monadMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | whiskerRightComp _ _ _ =>
      refine monadMonotoneMapOf_congr_of_spine_eq ?_
      rw [RawTwoCellExpr.castBoundary_spine]
      dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
      rw [composePath_assoc]
  | whiskerExchange _ _ _ => exact monadMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | vcompCongrLeft cellBeta _ ih => exact monadMonotoneMapOf_vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact monadMonotoneMapOf_vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerRightCongr oneCell ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★★ **The COMPLETE soundness leg `mapEqOfConv`.**  Every `MonadSaturatedTwoCellConv` derivation preserves the
monotone map: `ofFull` via `monadMonotoneMapOf_eqOfConvFull` (Godement invariance + spine-invariant whisker
functoriality); the three monad laws by the seed lemmas; the four congruences by the shipped congruence lemmas;
refl/symm/trans trivially.  This is the NO-direction of the walking-monad Δ decision. -/
theorem monadMonotoneMapOf_mapEqOfConv {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  induction conv with
  | ofFull h => exact monadMonotoneMapOf_eqOfConvFull h
  | leftUnit => exact monadMonotoneMapOf_leftUnit_eq_id
  | rightUnit => exact monadMonotoneMapOf_rightUnit_eq_id
  | assoc => exact monadMonotoneMapOf_assoc_eq
  | vcompCongrLeft cellBeta _ ih => exact monadMonotoneMapOf_vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact monadMonotoneMapOf_vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerRightCongr oneCell ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The soundness leg `mapEqOfConv` is COMPLETE: the Godement / `ofFull` residual is discharged by
`monadMonotoneMapOf_interchange` (the disjoint-window two-block commute, cap-free on Δ), and the full induction
`monadMonotoneMapOf_mapEqOfConv` assembles it with the shipped law + congruence legs.  What remains toward inhabiting
`MonadSaturatedCanonicalization` is the COMPLETENESS `convOfMapEq` (the EZ staircase).  `= true`. -/
def fxMonad_hasMapEqOfConvComplete : Bool := true

end FX1Poly.Polygraph
