import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordMultiplicativity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackConv

/-! # WalkingMonad — the RIGHT-whisker WORD MULTIPLICATIVITY (the named r11 blocker, closed)

`WalkingMonad/MonadWordMultiplicativity` closed the LEFT-whisker word multiplicativity (`wordMul_whiskerLeft`) and
shipped the RIGHT-whisker APPEND skeleton (`consAppend` + its domain-path / boundary identities), naming the
VCOMP-REASSEMBLY as the residual blocker: whiskering a canonical Eilenberg–Zilber word on the RIGHT by a `t`-power
passes THROUGH the head gadget's `hcomp = vcomp (whiskerRight _) (whiskerLeft _)` structure, and the two per-factor
`composePath`-associativity casts (one from `whiskerRightComp` on the left factor, one from `whiskerExchange` on the
right factor) must reconcile with the head-gadget's stored right context.

## What this file ships (each piece zero-axiom)

The reassembly is packaged as a REUSABLE, signature-generic distributivity law + two boundary-cast merge lemmas:

  * **`RawTwoCellExpr.vcomp_castBoundary_merge`** — two boundary casts sharing a MIDDLE seam fuse across a vertical
    composite: `vcomp (cast hs hm α) (cast hm ht β) = cast hs ht (vcomp α β)` (`cases`-collapse of the seams).
  * **`RawTwoCellExpr.vcomp_castBoundaryRight`** — the RIGHT-factor cast extrusion (the r11 named blocker), the
    dual of the shipped `vcomp_castBoundaryLeft`: a boundary cast on the RIGHT factor extrudes to the whole
    composite, the middle seam flipping onto the LEFT factor.
  * **`RawTwoCellExpr.hcomp_castBoundaryRight`** — pull a boundary cast out of the RIGHT `hcomp` factor.
  * ★ **`whiskerRight_hcomp`** — the DISTRIBUTIVITY: whiskering a horizontal composite on the right distributes
    into the right hcomp factor, `(α ⊠ β) ▷ W ≈ α ⊠ (β ▷ W)` (up to the associativity re-anchoring cast).  Proved
    by `whiskerRightVcomp` (split) + `whiskerRightComp` (left factor) + `whiskerExchange` (right factor) +
    `vcomp_castBoundary_merge` (the seam fusion).  Pure free-2-category, no monad law.
  * ★ **`wordMul_whiskerRight`** — `t^k ▷ (word counts) ≈ word (counts ++ 1^k)`, structural induction on `counts`:
    the head-gadget step is `whiskerRight_hcomp` (distribute), the induction hypothesis threads under the head
    gadget via `hcomp`-right-congruence, and `hcomp_castBoundaryRight` + `castBoundary_castBoundary` pull the cast
    out of the head gadget; the base is the ones-word collapse.  The RIGHT-whisker analog of `wordMul_whiskerLeft`
    — the RIGHT whisker appends a run of identity strands (a run of `1`s at the TAIL of the counts vector).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`List Nat` (the counts).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Boundary-cast algebra on vertical / horizontal composites (signature-generic) -/

/-- Two boundary casts sharing a MIDDLE seam FUSE across a vertical composite: casting a left factor's target seam
to the same 1-cell as a right factor's source seam and vertically composing is one boundary cast of the composite.
`cases` on all three seams collapses both sides. -/
theorem RawTwoCellExpr.vcomp_castBoundary_merge {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' middlePath middlePath' targetPath targetPath' :
      ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath')
    (htarget : targetPath = targetPath')
    (cellAlpha : RawTwoCellExpr signature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr signature middlePath targetPath) :
    RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha)
        (RawTwoCellExpr.castBoundary hmiddle htarget cellBeta)
      = RawTwoCellExpr.castBoundary hsource htarget (RawTwoCellExpr.vcomp cellAlpha cellBeta) := by
  cases hsource; cases hmiddle; cases htarget; rfl

/-- **RIGHT-factor cast extrusion** (the r11 named blocker), the dual of `vcomp_castBoundaryLeft`: a boundary cast
on the RIGHT factor of a vertical composite extrudes to the whole composite — the target seam survives, the middle
seam flips onto the LEFT factor. -/
theorem RawTwoCellExpr.vcomp_castBoundaryRight {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath middlePath middlePath' targetPath targetPath' :
      ModalityPath signature.graph sourceMode targetMode}
    (hmiddle : middlePath = middlePath') (htarget : targetPath = targetPath')
    (cellAlpha : RawTwoCellExpr signature sourcePath middlePath')
    (cellBeta : RawTwoCellExpr signature middlePath targetPath) :
    RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.castBoundary hmiddle htarget cellBeta)
      = RawTwoCellExpr.castBoundary rfl htarget
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.castBoundary rfl hmiddle.symm cellAlpha) cellBeta) := by
  cases hmiddle; cases htarget; rfl

/-- Pull a boundary cast out of the RIGHT `hcomp` factor: a cast on the right factor's boundary becomes a cast of
the whole horizontal composite, the whisker context `oneCellFDom` / `oneCellFCod` prepended by `congrArg`. -/
theorem RawTwoCellExpr.hcomp_castBoundaryRight {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGDom' oneCellGCod oneCellGCod' : ModalityPath signature.graph middleMode targetMode}
    (hdom : oneCellGDom = oneCellGDom') (hcod : oneCellGCod = oneCellGCod')
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    RawTwoCellExpr.hcomp cellAlpha (RawTwoCellExpr.castBoundary hdom hcod cellBeta)
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCellFDom) hdom)
          (congrArg (composePath oneCellFCod) hcod)
          (RawTwoCellExpr.hcomp cellAlpha cellBeta) := by
  cases hdom; cases hcod; rfl

/-! ## The RIGHT-whisker distributes into the RIGHT hcomp factor -/

/-- ★ **RIGHT-whisker / horizontal-composite distributivity.**  Whiskering a horizontal composite `α ⊠ β` on the
RIGHT by a 1-cell `W` distributes into the RIGHT factor: `(α ⊠ β) ▷ W ≈ α ⊠ (β ▷ W)`, up to the associativity
re-anchoring cast.  `hcomp α β` is `vcomp (whiskerRight β_dom α) (whiskerLeft α_cod β)`; `whiskerRightVcomp` splits
the right whisker over the vcomp, `whiskerRightComp` merges the two right whiskers on the left factor,
`whiskerExchange` swaps the right whisker past the left whisker on the right factor, and `vcomp_castBoundary_merge`
fuses the two per-factor associativity casts across the reassembled vertical composite.  Pure free-2-category —
no monad law. -/
theorem whiskerRight_hcomp {signature : ModeSignature}
    {sourceMode middleMode targetMode newTargetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (oneCell : ModalityPath signature.graph targetMode newTargetMode)
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.hcomp cellAlpha cellBeta))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc oneCellFDom oneCellGDom oneCell).symm
        (composePath_assoc oneCellFCod oneCellGCod oneCell).symm
        (RawTwoCellExpr.hcomp cellAlpha (RawTwoCellExpr.whiskerRight oneCell cellBeta))) := by
  refine TwoCellConvFull.trans
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep
      (TwoCellStep.whiskerRightVcomp oneCell
        (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha)
        (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)))) ?_
  have leftConv := TwoCellConvFull.ofCastLeft
    (composePath_assoc oneCellFDom oneCellGDom oneCell)
    (composePath_assoc oneCellFCod oneCellGDom oneCell)
    (TwoCellConvFull.symm (TwoCellConvFull.whiskerRightComp oneCellGDom oneCell cellAlpha))
  have rightConv := TwoCellConvFull.ofCastLeft
    (composePath_assoc oneCellFCod oneCellGDom oneCell)
    (composePath_assoc oneCellFCod oneCellGCod oneCell)
    (TwoCellConvFull.symm (TwoCellConvFull.whiskerExchange oneCellFCod oneCell cellBeta))
  refine TwoCellConvFull.trans (TwoCellConvFull.vcompCongrLeft _ leftConv) ?_
  refine TwoCellConvFull.trans (TwoCellConvFull.vcompCongrRight _ rightConv) ?_
  rw [RawTwoCellExpr.vcomp_castBoundary_merge]
  exact TwoCellConvFull.refl _

/-! ## The RIGHT-whisker word multiplicativity -/

/-- ★ **RIGHT-whisker word multiplicativity.**  Whiskering the canonical word of `counts` on the RIGHT by `t^k` is
saturated-convertible to the canonical word of the `k`-ones-APPENDED counts (the `k` new strands each hit their own
fresh TOP target once — the identity block at the top of the vector).  Structural induction on `counts`:

  * `counts = []` — `t^k ▷ id (t^0) ≈ id (t^k)` (`whiskerRightId`), and the ones word `word (1^k)` collapses to
    `id (t^k)` (`wordFromCounts_monadOnes_conv`), the boundary casts fusing.
  * `counts = c :: rest` — the head-gadget word `hcomp (gadget c) (word rest)` is right-whiskered: `whiskerRight_hcomp`
    distributes the `t^k` whisker into the RIGHT factor `word rest`, the induction hypothesis
    (`t^k ▷ word rest ≈ word (rest ++ 1^k)`) threads under the head gadget via the `hcomp`-right-congruence, and
    `hcomp_castBoundaryRight` + `castBoundary_castBoundary` pull the induction-hypothesis cast out of the head
    gadget and fuse it with the distributivity cast — landing exactly on `word (c :: (rest ++ 1^k)) =
    word ((c :: rest) ++ 1^k)`.

Pure free-2-category — no monad law.  The RIGHT dual of `wordMul_whiskerLeft`. -/
theorem wordMul_whiskerRight (k : Nat) : ∀ (counts : List Nat),
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (wordFromCounts counts))
      (RawTwoCellExpr.castBoundary (countsDomainPath_consAppend_ones counts k)
        (monadTPower_length_consAppend_ones counts k)
        (wordFromCounts (consAppend counts (monadOnes k))))
  | [] => by
      show MonadSaturatedTwoCellConv
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k)
            (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
          (RawTwoCellExpr.castBoundary (countsDomainPath_monadOnes k)
            (congrArg monadTPower (length_monadOnes k))
            (wordFromCounts (monadOnes k)))
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
          (TwoCellStep.whiskerRightId (signature := monadModeSignature) (monadTPower 0) (monadTPower k)))) ?_
      refine MonadSaturatedTwoCellConv.symm ?_
      have hstep := MonadSaturatedTwoCellConv.castBoundaryCongr
        (countsDomainPath_monadOnes k) (congrArg monadTPower (length_monadOnes k))
        (wordFromCounts_monadOnes_conv k)
      rw [monadCastBoundary_castBoundary, monadCastBoundary_id] at hstep
      exact hstep
  | c :: rest => by
      show MonadSaturatedTwoCellConv
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k)
            (RawTwoCellExpr.hcomp (monadGadget c) (wordFromCounts rest)))
          _
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.ofFull
          (whiskerRight_hcomp (monadTPower k) (monadGadget c) (wordFromCounts rest))) ?_
      have hcompRightCongr : MonadSaturatedTwoCellConv
          (RawTwoCellExpr.hcomp (monadGadget c)
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (wordFromCounts rest)))
          (RawTwoCellExpr.hcomp (monadGadget c)
            (RawTwoCellExpr.castBoundary (countsDomainPath_consAppend_ones rest k)
              (monadTPower_length_consAppend_ones rest k)
              (wordFromCounts (consAppend rest (monadOnes k))))) :=
        MonadSaturatedTwoCellConv.vcompCongrRight _
          (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT (wordMul_whiskerRight k rest))
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.castBoundaryCongr _ _ hcompRightCongr) ?_
      rw [RawTwoCellExpr.hcomp_castBoundaryRight, RawTwoCellExpr.castBoundary_castBoundary]
      exact MonadSaturatedTwoCellConv.refl _

/-! ## Honesty marker -/

/-- **ESTABLISHED — the RIGHT-whisker WORD MULTIPLICATIVITY is CLOSED, zero-axiom (the r11 named blocker resolved).**
Whiskering the canonical Eilenberg–Zilber word of `counts` on the RIGHT by a `t`-power `t^k` is
`MonadSaturatedTwoCellConv`-convertible to the canonical word of the `k`-ones-APPENDED counts
(`wordMul_whiskerRight` — `t^k ▷ word counts ≈ word (counts ++ 1^k)`).  The VCOMP-REASSEMBLY blocker (the two
per-factor associativity casts) is discharged by the reusable signature-generic distributivity `whiskerRight_hcomp`
(`(α ⊠ β) ▷ W ≈ α ⊠ (β ▷ W)`) — proved by `whiskerRightVcomp` + `whiskerRightComp` + `whiskerExchange` +
`vcomp_castBoundary_merge` (the seam fusion), plus the right-factor extrusion `vcomp_castBoundaryRight` shipped as
the named dual of `vcomp_castBoundaryLeft`.  Uses ONLY the completed free-strict-2-category laws — no monad law.
Both whisker-word multiplicativities (`wordMul_whiskerLeft` + `wordMul_whiskerRight`) are now CLOSED; what remains
toward the two whisker `normalizeCell` cases is the counts-alignment (`countsOf_embedLocalMap_left` / `_right`),
and the `vcomp` case still needs the vertical multiplicativity `wordMul_vcomp`.  `= true`. -/
def fxMonad_hasWordMulWhiskerRight : Bool := true

end FX1Poly.Polygraph
