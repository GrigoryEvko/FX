import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadVcompMultGen

/-! # WalkingMonad/MonadWordVcompGen — the VERTICAL word multiplicativity over the GENERIC carrier
(POLY-TAB r6 monad re-founding, WAVE 2, Brick B — the wall)

The monad-law-bearing `normalizeCell` `vcomp` brick, re-founded over `SaturatedConvOver monadModeSignature
MonadLawRel`: `wordGadgetCollapseGen` (a whole word absorbed into one merge gadget, the three monad laws) and
`wordMul_vcompGen` (`vcomp (word ccL) (cast (word ccR)) ~ cast (word (composeCounts ccL ccR))`, the block-sum
re-sort via the `wordMul_hcompGen` split + the free interchange + the per-block collapse + proof-irrelevant
cast fusion).  The carrier-only cast/data lemmas (`listSum`, `consTake`/`consDrop`, `composeCounts`,
`wordMul_vcomp_hmid`/`_hdom`, `monadGadget_cast`, `wordFromCounts_castEq`, `monadCastTripleEqCast`,
`RawTwoCellExpr.hcomp_castBoundaryLeft`) are REUSED by reference — casts act on the SYNTACTIC cells, identical in
both worlds; only the conv RELATION differs.

Raw Lean 4 + Init; zero-axiom; STRUCTURAL on the counts list.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The word-gadget collapse (the per-block monad-law merge), generic carrier -/

/-- The **gadget tail collapse**: `(gadget c ▷ t^r) ⊟ (t ◁ gadget r) ⊟ mu ≈ cast (gadget (c + r))` — reassociate,
peel `gadget (r+1)` (`gadgetSuccGen`), and fire the associativity crossing `gadgetRightMergeGen`. -/
theorem gadgetTailCollapseGen (leftWidth rightWidth : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (monadGadget leftWidth))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth)))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth))) := by
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth))
        monadMulTwoCell))) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
        (monadGadget leftWidth))
      (gadgetSuccGen rightWidth)) ?_
  exact gadgetRightMergeGen leftWidth rightWidth

/-- ★ **The word-gadget collapse.**  Merging a canonical word `word cc` then the `cc.length`-fold merge gadget
absorbs to a single `(listSum cc)`-fold merge: `vcomp (word cc) (gadget cc.length) ≈ cast (gadget (listSum cc))`.
Structural induction on `cc`.  Base `cc = []` is `vcomp (id t^0) eta ≈ eta` (`vcompIdLeft`).  The `c :: rest`
step: peel `gadget (rest.length + 1)` (`gadgetSuccGen`, reassociate), distribute the head `hcomp`, merge the two
`t`-left-whiskers over the inner vcomp (`whiskerLeftVcomp`), thread the induction hypothesis under the `t`-whisker
(collapsing `word rest ⊟ gadget rest.length`), extrude the boundary cast (`monadWhiskerLeft_castBoundary`), rewrite
the head-gadget right-whisker context `countsDomainPath rest` to `t^(listSum rest)` (`whiskerRight_pathCongr` +
the domain bridge), re-peel `gadget (listSum rest + 1)` (`gadgetSuccGen`), and fire the associativity crossing
`gadgetRightMergeGen c (listSum rest)` — `c + listSum rest = listSum (c :: rest)`.  Uses the three monad laws via
`gadgetSuccGen` / `gadgetRightMergeGen`. -/
theorem wordGadgetCollapseGen : ∀ (cc : List Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (wordFromCounts cc) (monadGadget cc.length))
      (RawTwoCellExpr.castBoundary (countsDomainPath_eq_monadTPower_listSum cc).symm rfl
        (monadGadget (listSum cc)))
  | [] =>
      SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (monadGadget 0)))
  | count :: rest => by
      -- LHS = vcomp (hcomp (gadget count) (word rest)) (gadget (rest.length + 1)).
      -- Peel gadget (rest.length + 1) via gadgetSuccGen, then reassociate.
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrRight
          (RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest))
          (SaturatedConvOver.symm (gadgetSuccGen rest.length))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.symm
          (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rest.length))
              monadMulTwoCell)))) ?_
      -- The inner `vcomp (hcomp gc W) (t ◁ gadget rest.length)`; expand hcomp and reassociate.
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
                (monadGadget count))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rest.length)))))) ?_
      -- Merge the two `t`-left-whiskers over the inner vcomp.
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.vcompCongrRight
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
              (monadGadget count))
            (SaturatedConvOver.symm
              (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
                (TwoCellStep.whiskerLeftVcomp monadT (wordFromCounts rest) (monadGadget rest.length))))))) ?_
      -- Thread the induction hypothesis under the `t`-whisker.
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.vcompCongrRight
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
              (monadGadget count))
            (SaturatedConvOver.whiskerLeftCongr monadT (wordGadgetCollapseGen rest)))) ?_
      -- Extrude the boundary cast out of the `t`-whisker.
      rw [monadWhiskerLeft_castBoundary]
      -- Rewrite the head-gadget right-whisker context to `t^(listSum rest)`.
      rw [RawTwoCellExpr.whiskerRight_pathCongr (countsDomainPath_eq_monadTPower_listSum rest)
            (monadGadget count)]
      -- Merge the two inner casts (lift the `Eq` through `vcompCongrLeft`, motive-safe via `ofEq`).
      have hmerge :=
        RawTwoCellExpr.vcomp_castBoundary_merge
          (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
          (congrArg (composePath monadT) (countsDomainPath_eq_monadTPower_listSum rest).symm)
          (congrArg (composePath monadT)
            (rfl : (monadT : ModalityPath monadGraph MonadMode.point MonadMode.point) = monadT))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
            (monadGadget count))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest)))
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.ofEq hmerge)) ?_
      -- Extrude the outer-left cast (as an `Eq`, `rfl`-cast on `mu` collapses definitionally), fire the tail.
      have hextrude : RawTwoCellExpr.vcomp
            (RawTwoCellExpr.castBoundary
              (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
              (congrArg (composePath monadT)
                (rfl : (monadT : ModalityPath monadGraph MonadMode.point MonadMode.point) = monadT))
              (RawTwoCellExpr.vcomp
                (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
                  (monadGadget count))
                (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest)))))
            monadMulTwoCell
          = RawTwoCellExpr.castBoundary
              (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
              rfl
              (RawTwoCellExpr.vcomp
                (RawTwoCellExpr.vcomp
                  (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
                    (monadGadget count))
                  (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest))))
                monadMulTwoCell) :=
        RawTwoCellExpr.vcomp_castBoundaryLeft _ _ _ _
      refine SaturatedConvOver.trans (SaturatedConvOver.ofEq hextrude) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ rfl (gadgetTailCollapseGen count (listSum rest))) ?_
      rw [monadCastBoundary_castBoundary]
      exact SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-! ## The free interchange + the two-factor collapse, generic carrier -/

/-- ★ **The free interchange (symm direction), packaged for the saturated relation.**  A vertical composite of two
horizontal composites is the horizontal composite of the two vertical composites: `(A ⊠ B) ⊟ (C ⊠ D) ≈ (A ⊟ C) ⊠
(B ⊟ D)` — cast-free, both Godement orders sharing the boundary (`TwoCellStep.interchange`, symmetrised).  This is
the interchange / Godement bifunctoriality that the `wordMul_vcompGen` block re-sort turns on. -/
theorem monadVcompHcompSplitGen {sourceMode middleMode targetMode : MonadMode}
    {pathZero pathOne pathTwo : ModalityPath monadModeSignature.graph sourceMode middleMode}
    {pathZeroBack pathOneBack pathTwoBack : ModalityPath monadModeSignature.graph middleMode targetMode}
    (cellA : RawTwoCellExpr monadModeSignature pathZero pathOne)
    (cellC : RawTwoCellExpr monadModeSignature pathOne pathTwo)
    (cellB : RawTwoCellExpr monadModeSignature pathZeroBack pathOneBack)
    (cellD : RawTwoCellExpr monadModeSignature pathOneBack pathTwoBack) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellA cellB) (RawTwoCellExpr.hcomp cellC cellD))
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellA cellC) (RawTwoCellExpr.vcomp cellB cellD)) :=
  SaturatedConvOver.symm
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.interchange cellA cellC cellB cellD)))

/-- The two-factor COLLAPSE of the interchanged composite: the front vertical composite `word take ⊟ gadget r-cast`
collapses to `gadget (listSum take)` (`wordGadgetCollapseGen`, absorbing the block into one merge), and the back
vertical composite `word drop ⊟ word ccR'-cast` is the induction hypothesis; horizontally re-composing gives the
head-gadget word of the next block sum.  Uses the two saturated hcomp congruences (`hcompCongrLeft` / `Right`). -/
theorem monadWordVcompStepCollapseGen (r : Nat) (take drop ccR' : List Nat)
    (htake : take.length = r) (hdrop : drop.length = listSum ccR')
    (ih : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (wordFromCounts drop)
        (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid drop ccR' hdrop) rfl (wordFromCounts ccR')))
      (RawTwoCellExpr.castBoundary (wordMul_vcomp_hdom drop ccR' hdrop)
        (congrArg monadTPower (composeCounts_length drop ccR'))
        (wordFromCounts (composeCounts drop ccR')))) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.vcomp (wordFromCounts take)
          (RawTwoCellExpr.castBoundary (congrArg monadTPower htake.symm) rfl (monadGadget r)))
        (RawTwoCellExpr.vcomp (wordFromCounts drop)
          (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid drop ccR' hdrop) rfl (wordFromCounts ccR'))))
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.castBoundary (countsDomainPath_eq_monadTPower_listSum take).symm rfl
          (monadGadget (listSum take)))
        (RawTwoCellExpr.castBoundary (wordMul_vcomp_hdom drop ccR' hdrop)
          (congrArg monadTPower (composeCounts_length drop ccR'))
          (wordFromCounts (composeCounts drop ccR')))) := by
  have hFrontCollapse : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (wordFromCounts take)
        (RawTwoCellExpr.castBoundary (congrArg monadTPower htake.symm) rfl (monadGadget r)))
      (RawTwoCellExpr.castBoundary
        (countsDomainPath_eq_monadTPower_listSum take).symm rfl (monadGadget (listSum take))) := by
    refine SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight (wordFromCounts take)
        (SaturatedConvOver.ofEq (monadGadget_cast r take.length htake.symm))) ?_
    exact wordGadgetCollapseGen take
  refine SaturatedConvOver.trans
    (SaturatedConvOver.hcompCongrLeft hFrontCollapse _) ?_
  exact SaturatedConvOver.hcompCongrRight _ ih

/-! ## ★★ The VERTICAL word multiplicativity, generic carrier -/

/-- ★★ **The VERTICAL word multiplicativity.**  Vertically composing two canonical Eilenberg–Zilber words is the
canonical word of their block-sum composition (`composeCounts`), up to the boundary casts: given the partition
`ccL.length = listSum ccR`, `vcomp (word ccL) (cast (word ccR)) ≈ cast (word (composeCounts ccL ccR))`.  This is the
monad-law-bearing `normalizeCell` `vcomp` case — the second saturated decision of the ladder, closing #2008/#2009.
Structural recursion on `ccR`:

  * `ccR = []` — the partition forces `ccL = []`; both words are `id (t^0)`, convertible by `vcompIdRight` and cast
    collapse.
  * `ccR = r :: ccR'` — split `ccL` at the first block via `consTake r` / `consDrop r`; `wordMul_hcompGen` rewrites
    `word ccL` as the horizontal composite `word take ⊠ word drop`, the free interchange `monadVcompHcompSplitGen`
    swaps the vertical-of-horizontal into horizontal-of-vertical, the front vertical composite collapses to
    `gadget (listSum take)` (`wordGadgetCollapseGen`) and the back is the induction hypothesis, and re-composing
    horizontally lands on `word (listSum take :: composeCounts drop ccR') = word (composeCounts ccL (r :: ccR'))`.
    The `monadTPower_add` middle cast lets the cast-free interchange fire; the accumulated boundary casts are fused
    by `monadCastTripleEqCast` (proof-irrelevant seams) and reconciled to the target by `castBoundary_wordCongr`.

Uses the three monad laws through `wordGadgetCollapseGen`.  Raw, zero-axiom, STRUCTURAL on the counts list. -/
theorem wordMul_vcompGen : ∀ (ccR ccL : List Nat) (hlen : ccL.length = listSum ccR),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (wordFromCounts ccL)
        (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid ccL ccR hlen) rfl (wordFromCounts ccR)))
      (RawTwoCellExpr.castBoundary (wordMul_vcomp_hdom ccL ccR hlen)
        (congrArg monadTPower (composeCounts_length ccL ccR))
        (wordFromCounts (composeCounts ccL ccR)))
  | [], ccL, hlen => by
      cases ccL with
      | cons head tail => exact absurd hlen (fun heq => Nat.noConfusion heq)
      | nil =>
          refine SaturatedConvOver.trans
            (SaturatedConvOver.vcompCongrRight (wordFromCounts [])
              (SaturatedConvOver.ofEq (monadCastBoundary_id _ _))) ?_
          refine SaturatedConvOver.trans
            (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
              (TwoCellStep.vcompIdRight (wordFromCounts [])))) ?_
          exact SaturatedConvOver.symm
            (SaturatedConvOver.ofEq (monadCastBoundary_id _ _))
  | r :: ccR', ccL, hlen => by
      have hr : r ≤ ccL.length := by
        rw [hlen]; exact Nat.le_add_right r (listSum ccR')
      have htake : (consTake r ccL).length = r := consTake_length_of_le r ccL hr
      have hdrop : (consDrop r ccL).length = listSum ccR' := by
        rw [consDrop_length, hlen]; exact natAddSubCancelLeft r (listSum ccR')
      have hsplit : consAppend (consTake r ccL) (consDrop r ccL) = ccL :=
        consAppend_consTake_consDrop r ccL
      have ih := wordMul_vcompGen ccR' (consDrop r ccL) hdrop
      -- bridge: word ccL ~ single-cast of hcomp (word take) (word drop)
      have hbridge : SaturatedConvOver monadModeSignature MonadLawRel (wordFromCounts ccL)
          (RawTwoCellExpr.castBoundary
            (((countsDomainPath_consAppend (consTake r ccL) (consDrop r ccL)).symm).trans
              (congrArg countsDomainPath hsplit.symm.symm))
            (((monadTPower_length_consAppend (consTake r ccL) (consDrop r ccL)).symm).trans
              (congrArg (fun list => monadTPower list.length) hsplit.symm.symm))
            (RawTwoCellExpr.hcomp (wordFromCounts (consTake r ccL)) (wordFromCounts (consDrop r ccL)))) := by
        refine SaturatedConvOver.trans
          (SaturatedConvOver.ofEq
            (wordFromCounts_castEq ccL (consAppend (consTake r ccL) (consDrop r ccL)) hsplit.symm)) ?_
        refine SaturatedConvOver.trans
          (SaturatedConvOver.castBoundaryCongr _ _
            (wordMul_hcompGen (consTake r ccL) (consDrop r ccL))) ?_
        exact SaturatedConvOver.ofEq
          (RawTwoCellExpr.castBoundary_castBoundary _ _ _ _
            (RawTwoCellExpr.hcomp (wordFromCounts (consTake r ccL)) (wordFromCounts (consDrop r ccL))))
      -- apply the bridge on the LEFT factor, then extrude the outer source cast
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft _ hbridge) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofEq
          (RawTwoCellExpr.vcomp_castBoundaryLeft _ _
            (RawTwoCellExpr.hcomp (wordFromCounts (consTake r ccL)) (wordFromCounts (consDrop r ccL)))
            (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid ccL (r :: ccR') hlen) rfl
              (wordFromCounts (r :: ccR'))))) ?_
      -- recognise the middle-cast of `word (r :: ccR')` as the hcomp of the two interchange factors
      have hMiddle : RawTwoCellExpr.castBoundary
            ((((monadTPower_length_consAppend (consTake r ccL) (consDrop r ccL)).symm).trans
              (congrArg (fun list => monadTPower list.length) hsplit.symm.symm)).symm) rfl
            (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid ccL (r :: ccR') hlen) rfl
              (wordFromCounts (r :: ccR')))
          = RawTwoCellExpr.hcomp
              (RawTwoCellExpr.castBoundary (congrArg monadTPower htake.symm) rfl (monadGadget r))
              (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid (consDrop r ccL) ccR' hdrop) rfl
                (wordFromCounts ccR')) := by
        rw [RawTwoCellExpr.castBoundary_castBoundary,
            RawTwoCellExpr.hcomp_castBoundaryLeft, RawTwoCellExpr.hcomp_castBoundaryRight,
            RawTwoCellExpr.castBoundary_castBoundary]
        rfl
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (SaturatedConvOver.vcompCongrRight
            (RawTwoCellExpr.hcomp (wordFromCounts (consTake r ccL)) (wordFromCounts (consDrop r ccL)))
            (SaturatedConvOver.ofEq hMiddle))) ?_
      -- interchange, then the two-factor collapse
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (monadVcompHcompSplitGen (wordFromCounts (consTake r ccL))
            (RawTwoCellExpr.castBoundary (congrArg monadTPower htake.symm) rfl (monadGadget r))
            (wordFromCounts (consDrop r ccL))
            (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid (consDrop r ccL) ccR' hdrop) rfl
              (wordFromCounts ccR')))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (monadWordVcompStepCollapseGen r (consTake r ccL) (consDrop r ccL) ccR' htake hdrop ih)) ?_
      -- extrude the collapsed hcomp and reconcile with the target cast (same word, proof-irrelevant seams)
      refine SaturatedConvOver.ofEq ?_
      rw [RawTwoCellExpr.hcomp_castBoundaryLeft, RawTwoCellExpr.hcomp_castBoundaryRight]
      exact monadCastTripleEqCast _ _ _ _ _ _ _ _ _

/-! ## Non-vacuity smoke -/

/-- Smoke: two identity strands vertically composed with the width-2 merge gadget IS the merge —
`vcomp (word [1,1]) (cast (word [2])) ≈ cast (word (composeCounts [1,1] [2]))`, and
`composeCounts [1,1] [2] = [2]` (the two mid strands merge to one target).  A genuine `t^2 ⇒ t` instance. -/
theorem wordMul_vcomp_smoke_mergeGen :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp (wordFromCounts [1, 1])
        (RawTwoCellExpr.castBoundary (wordMul_vcomp_hmid [1, 1] [2] rfl) rfl (wordFromCounts [2])))
      (RawTwoCellExpr.castBoundary (wordMul_vcomp_hdom [1, 1] [2] rfl)
        (congrArg monadTPower (composeCounts_length [1, 1] [2]))
        (wordFromCounts (composeCounts [1, 1] [2]))) :=
  wordMul_vcompGen [2] [1, 1] rfl

/-- **ESTABLISHED — the VERTICAL word multiplicativity is re-founded GENERIC-NATIVE.**  `wordGadgetCollapseGen`
(the per-block monad-law merge) and `wordMul_vcompGen` over `SaturatedConvOver monadModeSignature MonadLawRel`,
bespoke-free — the sole `normalizeCell` case using the monad LAWS, ported ctor-for-ctor.  The historic proof-
irrelevant cast-fusion crux (`monadCastTripleEqCast`, `RawTwoCellExpr.*` casts) does NOT reappear: casts act on the
shared syntactic cells.  `= true`. -/
def fxMonad_hasWordMulVcompGen : Bool := true

end FX1Poly.Polygraph.Amalgam
