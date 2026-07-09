import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerCountsAlign
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackConv

/-! # WalkingMonad — the two WHISKER `normalizeCell` cases (`whiskerLeft/Right W body ≈ canon`)

`MonadWhiskerCountsAlign` closed the counts-alignment (`canonCounts_whiskerLeft/Right`), and `MonadWordMultiplicativity`
/ `MonadWhiskerRightMult` closed the whisker word multiplicativities.  This file assembles the two WHISKER cases of
the cell-level normalization `normalizeCell : cell ≈ canon cell` — the fourth and fifth of the five `normalizeCell`
constructors, after the two `gen` leaves and the `id` case.

## The assembly (each case)

Given the induction hypothesis `body ≈ canon body`:

  1. `whiskerLeft/Right W body ≈ whiskerLeft/Right W (canon body)` (the shipped whisker congruence).
  2. `canon body` is a boundary cast of `word (canonCounts body)`; the whisker commutes with that cast
     (`whiskerLeft/Right_castBoundary`).
  3. On Δ every 1-cell is a `t`-power (`monadPath_normalForm : W = t^W.length`), so the whisker over `W` transports
     to a whisker over `t^W.length` (`whiskerLeft/Right_pathCongr`).
  4. The whisker word multiplicativity `wordMul_whiskerLeft/Right` rewrites `t^k ◁/▷ word cc` to the canonical word
     of the `1`-run prefixed / appended counts.
  5. That counts vector IS `canonCounts (whiskerLeft/Right W body)` (`canonCounts_whiskerLeft/Right`), so the two
     boundary casts collapse and the result is `canon (whiskerLeft/Right W body)` (boundary casts proof-irrelevant).

## What this file ships (each piece zero-axiom)

  * **`RawTwoCellExpr.whiskerLeft_pathCongr` / `whiskerRight_pathCongr`** — transport a whisker across a 1-cell
    equality (the `W = t^W.length` boundary transport).
  * **`RawTwoCellExpr.castBoundary_double_collapse`** — a double boundary cast collapses to a single cast to the
    same endpoints (the two whisker-fusion + word-multiplicativity casts reconcile).
  * ★ **`monadNormalize_whiskerLeft` / `monadNormalize_whiskerRight`** — the two WHISKER `normalizeCell` cases.

With the two `gen` leaves (`MonadNormalizeCases`), the `id` case (`MonadNormalizeCases`), and these two whisker
cases now closed, the SOLE remaining `normalizeCell` case is `vcomp` (the vertical word multiplicativity
`wordMul_vcomp`, using the monad laws), toward inhabiting `normalize : MonadNormalizesToCanon`.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Whisker 1-cell transport + double-cast collapse (signature-generic) -/

/-- Transport a LEFT whisker across a 1-cell equality (the `W = t^W.length` boundary transport). -/
theorem RawTwoCellExpr.whiskerLeft_pathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellA oneCellB : ModalityPath signature.graph sourceMode middleMode}
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    (hpath : oneCellA = oneCellB) (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCellA body
      = RawTwoCellExpr.castBoundary (congrArg (fun p => composePath p oneCellG) hpath.symm)
          (congrArg (fun p => composePath p oneCellH) hpath.symm)
          (RawTwoCellExpr.whiskerLeft oneCellB body) := by
  cases hpath; rfl

/-- Transport a RIGHT whisker across a 1-cell equality (the right dual). -/
theorem RawTwoCellExpr.whiskerRight_pathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellA oneCellB : ModalityPath signature.graph middleMode targetMode}
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode}
    (hpath : oneCellA = oneCellB) (body : RawTwoCellExpr signature bodyDom bodyCod) :
    RawTwoCellExpr.whiskerRight oneCellA body
      = RawTwoCellExpr.castBoundary (congrArg (composePath bodyDom) hpath.symm)
          (congrArg (composePath bodyCod) hpath.symm)
          (RawTwoCellExpr.whiskerRight oneCellB body) := by
  cases hpath; rfl

/-- Two successive boundary casts collapse to a single cast to the same endpoints (proof-irrelevant seams). -/
theorem RawTwoCellExpr.castBoundary_double_collapse {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {p0 p1 p2 q0 q1 q2 : ModalityPath signature.graph sourceMode targetMode}
    (hs1 : p0 = p1) (ht1 : q0 = q1) (hs2 : p1 = p2) (ht2 : q1 = q2)
    (hs : p0 = p2) (ht : q0 = q2) (cell : RawTwoCellExpr signature p0 q0) :
    RawTwoCellExpr.castBoundary hs2 ht2 (RawTwoCellExpr.castBoundary hs1 ht1 cell)
      = RawTwoCellExpr.castBoundary hs ht cell := by
  cases hs1; cases ht1; cases hs2; cases ht2; rfl

/-! ## The LEFT whisker `normalizeCell` case -/

/-- ★ **Case `whiskerLeft W body` of `normalize`.**  Every left-whiskered free 2-cell is
`MonadSaturatedTwoCellConv`-convertible to the canonical word of its own fold, given the body already is.  The
canonical word of `whiskerLeft W body` is the body's canonical word with a `1`-run of length `W.length` prepended
(`canonCounts_whiskerLeft`); the conversion threads the induction hypothesis under the left whisker, pulls the cast
out of the body's canonical form, transports `W` to `t^W.length` (`monadPath_normalForm`), applies the LEFT whisker
word multiplicativity (`wordMul_whiskerLeft`), and collapses the boundary casts.  Pure free-2-category — no monad
law. -/
theorem monadNormalize_whiskerLeft {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadModeSignature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (ih : MonadSaturatedTwoCellConv body (canon body)) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell body)
      (canon (RawTwoCellExpr.whiskerLeft oneCell body)) := by
  have hD : countsDomainPath (consReplicate 1 oneCell.length (canonCounts body))
      = composePath oneCell oneCellG := by
    rw [countsDomainPath_consReplicate_one, canonDomain_eq body]
    exact congrArg (fun p => composePath p oneCellG) (monadPath_normalForm oneCell).symm
  have hC : monadTPower (consReplicate 1 oneCell.length (canonCounts body)).length
      = composePath oneCell oneCellH := by
    rw [monadTPower_length_consReplicate_one, canonCodomain_eq body]
    exact congrArg (fun p => composePath p oneCellH) (monadPath_normalForm oneCell).symm
  rw [show canon (RawTwoCellExpr.whiskerLeft oneCell body)
        = RawTwoCellExpr.castBoundary hD hC
            (wordFromCounts (consReplicate 1 oneCell.length (canonCounts body)))
      from RawTwoCellExpr.castBoundary_wordCongr
        (canonDomain_eq (RawTwoCellExpr.whiskerLeft oneCell body))
        (canonCodomain_eq (RawTwoCellExpr.whiskerLeft oneCell body)) hD hC
        (canonCounts_whiskerLeft oneCell body)]
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.whiskerLeftCongr oneCell ih) ?_
  have outS : composePath oneCell (countsDomainPath (canonCounts body)) = composePath oneCell oneCellG :=
    congrArg (composePath oneCell) (canonDomain_eq body)
  have outT : composePath oneCell (monadTPower (canonCounts body).length) = composePath oneCell oneCellH :=
    congrArg (composePath oneCell) (canonCodomain_eq body)
  have pcS : composePath (monadTPower oneCell.length) (countsDomainPath (canonCounts body))
      = composePath oneCell (countsDomainPath (canonCounts body)) :=
    congrArg (fun p => composePath p (countsDomainPath (canonCounts body)))
      (monadPath_normalForm oneCell).symm
  have pcT : composePath (monadTPower oneCell.length) (monadTPower (canonCounts body).length)
      = composePath oneCell (monadTPower (canonCounts body).length) :=
    congrArg (fun p => composePath p (monadTPower (canonCounts body).length))
      (monadPath_normalForm oneCell).symm
  have hEq1 : RawTwoCellExpr.whiskerLeft oneCell (canon body)
      = RawTwoCellExpr.castBoundary (pcS.trans outS) (pcT.trans outT)
          (RawTwoCellExpr.whiskerLeft (monadTPower oneCell.length)
            (wordFromCounts (canonCounts body))) := by
    show RawTwoCellExpr.whiskerLeft oneCell
        (RawTwoCellExpr.castBoundary (canonDomain_eq body) (canonCodomain_eq body)
          (wordFromCounts (canonCounts body)))
      = _
    rw [RawTwoCellExpr.whiskerLeft_castBoundary,
        RawTwoCellExpr.whiskerLeft_pathCongr (monadPath_normalForm oneCell),
        RawTwoCellExpr.castBoundary_castBoundary]
    rfl
  rw [hEq1]
  have hcol := RawTwoCellExpr.castBoundary_double_collapse
    (countsDomainPath_consReplicate_one oneCell.length (canonCounts body))
    (monadTPower_length_consReplicate_one oneCell.length (canonCounts body))
    (pcS.trans outS) (pcT.trans outT) hD hC
    (wordFromCounts (consReplicate 1 oneCell.length (canonCounts body)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.castBoundaryCongr (pcS.trans outS) (pcT.trans outT)
      (wordMul_whiskerLeft oneCell.length (canonCounts body))) ?_
  exact hcol ▸ MonadSaturatedTwoCellConv.refl _

/-! ## The RIGHT whisker `normalizeCell` case -/

/-- ★ **Case `whiskerRight W body` of `normalize`.**  The right dual: every right-whiskered free 2-cell is
convertible to its own canonical word, whose counts is the body's counts with a `1`-run of length `W.length`
APPENDED (`canonCounts_whiskerRight`).  Same assembly through `whiskerRightCongr` + `whiskerRight_castBoundary` +
`whiskerRight_pathCongr` + `wordMul_whiskerRight` + the boundary-cast collapse.  Pure free-2-category — no monad
law. -/
theorem monadNormalize_whiskerRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph sourceMode middleMode}
    (oneCell : ModalityPath monadModeSignature.graph middleMode targetMode)
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (ih : MonadSaturatedTwoCellConv body (canon body)) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell body)
      (canon (RawTwoCellExpr.whiskerRight oneCell body)) := by
  have hD : countsDomainPath (consAppend (canonCounts body) (monadOnes oneCell.length))
      = composePath oneCellF oneCell := by
    rw [countsDomainPath_consAppend_ones, canonDomain_eq body]
    exact congrArg (composePath oneCellF) (monadPath_normalForm oneCell).symm
  have hC : monadTPower (consAppend (canonCounts body) (monadOnes oneCell.length)).length
      = composePath oneCellG oneCell := by
    rw [monadTPower_length_consAppend_ones, canonCodomain_eq body]
    exact congrArg (composePath oneCellG) (monadPath_normalForm oneCell).symm
  rw [show canon (RawTwoCellExpr.whiskerRight oneCell body)
        = RawTwoCellExpr.castBoundary hD hC
            (wordFromCounts (consAppend (canonCounts body) (monadOnes oneCell.length)))
      from RawTwoCellExpr.castBoundary_wordCongr
        (canonDomain_eq (RawTwoCellExpr.whiskerRight oneCell body))
        (canonCodomain_eq (RawTwoCellExpr.whiskerRight oneCell body)) hD hC
        (canonCounts_whiskerRight oneCell body)]
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.whiskerRightCongr oneCell ih) ?_
  have outS : composePath (countsDomainPath (canonCounts body)) oneCell = composePath oneCellF oneCell :=
    congrArg (fun p => composePath p oneCell) (canonDomain_eq body)
  have outT : composePath (monadTPower (canonCounts body).length) oneCell = composePath oneCellG oneCell :=
    congrArg (fun p => composePath p oneCell) (canonCodomain_eq body)
  have pcS : composePath (countsDomainPath (canonCounts body)) (monadTPower oneCell.length)
      = composePath (countsDomainPath (canonCounts body)) oneCell :=
    congrArg (composePath (countsDomainPath (canonCounts body))) (monadPath_normalForm oneCell).symm
  have pcT : composePath (monadTPower (canonCounts body).length) (monadTPower oneCell.length)
      = composePath (monadTPower (canonCounts body).length) oneCell :=
    congrArg (composePath (monadTPower (canonCounts body).length)) (monadPath_normalForm oneCell).symm
  have hEq1 : RawTwoCellExpr.whiskerRight oneCell (canon body)
      = RawTwoCellExpr.castBoundary (pcS.trans outS) (pcT.trans outT)
          (RawTwoCellExpr.whiskerRight (monadTPower oneCell.length)
            (wordFromCounts (canonCounts body))) := by
    show RawTwoCellExpr.whiskerRight oneCell
        (RawTwoCellExpr.castBoundary (canonDomain_eq body) (canonCodomain_eq body)
          (wordFromCounts (canonCounts body)))
      = _
    rw [RawTwoCellExpr.whiskerRight_castBoundary,
        RawTwoCellExpr.whiskerRight_pathCongr (monadPath_normalForm oneCell),
        RawTwoCellExpr.castBoundary_castBoundary]
    rfl
  rw [hEq1]
  have hcol := RawTwoCellExpr.castBoundary_double_collapse
    (countsDomainPath_consAppend_ones (canonCounts body) oneCell.length)
    (monadTPower_length_consAppend_ones (canonCounts body) oneCell.length)
    (pcS.trans outS) (pcT.trans outT) hD hC
    (wordFromCounts (consAppend (canonCounts body) (monadOnes oneCell.length)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.castBoundaryCongr (pcS.trans outS) (pcT.trans outT)
      (wordMul_whiskerRight oneCell.length (canonCounts body))) ?_
  exact hcol ▸ MonadSaturatedTwoCellConv.refl _

/-! ## Honesty marker -/

/-- **ESTABLISHED — the two WHISKER `normalizeCell` cases are CLOSED, zero-axiom.**  Every left/right-whiskered
free 2-cell is `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of its own fold
(`monadNormalize_whiskerLeft` / `monadNormalize_whiskerRight`), assembled from the induction hypothesis under the
whisker congruence, the whisker/boundary-cast commutation, the `W = t^W.length` boundary transport
(`whiskerLeft/Right_pathCongr` + `monadPath_normalForm`), the whisker word multiplicativity
(`wordMul_whiskerLeft/Right`), and the counts-alignment (`canonCounts_whiskerLeft/Right`) — using ONLY the completed
free-strict-2-category laws, no monad law.  With the two `gen` leaves and the `id` case, FOUR of the five
`normalizeCell` cases are now closed; the SOLE remaining case is `vcomp` (the vertical word multiplicativity
`wordMul_vcomp`, which alone uses the monad LAWS).  Until `vcomp` lands, `normalize : MonadNormalizesToCanon` is not
inhabited, so `MonadSaturatedCanonicalization.convOfMapEq` is not inhabited and the three completeness flags stay
`false`.  `= true`. -/
def fxMonad_hasWhiskerNormalizeCases : Bool := true

end FX1Poly.Polygraph
