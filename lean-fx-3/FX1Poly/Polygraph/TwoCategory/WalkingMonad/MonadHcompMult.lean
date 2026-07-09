import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerNormalizeCases

/-! # WalkingMonad — horizontal-composite ASSOCIATIVITY + word HORIZONTAL multiplicativity

The `vcomp` `normalizeCell` case reduces to the VERTICAL word multiplicativity `wordMul_vcomp`, which in turn
needs the HORIZONTAL word multiplicativity `wordMul_hcomp` — a canonical word of an appended counts list is the
horizontal composite of the two sub-words.  That rests on the free-strict-2-category law the lane never built:
**associativity of horizontal composition** `α ⊠ (β ⊠ γ) ≈ (α ⊠ β) ⊠ γ` (up to the 1-cell associator).

## What this file ships (each piece zero-axiom)

  * ★ **`hcompAssoc`** — the associativity of the derived Godement product, signature-generic on `TwoCellConvFull`.
    Both sides distribute into a three-fold vertical composite (`whiskerLeftVcomp` / `whiskerRightVcomp`), which
    match term-by-term by `whiskerRightComp` (the `α`-column), `whiskerExchange` (the `β`-column), and
    `whiskerLeftComp` (the `γ`-column); the per-column associator casts fuse across the composite via
    `vcomp_castBoundary_merge`.  Pure free-2-category — no monad law.
  * ★ **`wordMul_hcomp`** — `word (a ++ b) ≈ (word a) ⊠ (word b)` (up to the domain associator cast), structural
    induction on `a`: the head-gadget step re-brackets `gadget c ⊠ (word a' ⊠ word b)` to `(gadget c ⊠ word a') ⊠
    word b` by `hcompAssoc`, threading the induction hypothesis under the head gadget.  Pure free-2-category.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`List Nat` (the counts).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Associativity of horizontal composition (signature-generic) -/

/-- ★ **Associativity of the Godement horizontal product.**  Whiskering-and-vcomp'ing three 2-cells composes
associatively up to the 1-cell associator: `α ⊠ (β ⊠ γ) ≈ cast (α ⊠ β) ⊠ γ`.  Both sides expand (via the two
whisker-over-vcomp distributions) to the SAME three-column vertical composite — the `α`-column matched by
`whiskerRightComp`, the `β`-column by the disjoint-whisker `whiskerExchange`, the `γ`-column by `whiskerLeftComp`
— and the three per-column associator casts fuse to one outer cast by `vcomp_castBoundary_merge`.  No monad law. -/
theorem hcompAssoc {signature : ModeSignature}
    {modeS modeM1 modeM2 modeT : signature.graph.Mode}
    {oneCellA0 oneCellA1 : ModalityPath signature.graph modeS modeM1}
    {oneCellB0 oneCellB1 : ModalityPath signature.graph modeM1 modeM2}
    {oneCellC0 oneCellC1 : ModalityPath signature.graph modeM2 modeT}
    (cellAlpha : RawTwoCellExpr signature oneCellA0 oneCellA1)
    (cellBeta : RawTwoCellExpr signature oneCellB0 oneCellB1)
    (cellGamma : RawTwoCellExpr signature oneCellC0 oneCellC1) :
    TwoCellConvFull signature
      (RawTwoCellExpr.hcomp cellAlpha (RawTwoCellExpr.hcomp cellBeta cellGamma))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc oneCellA0 oneCellB0 oneCellC0)
        (composePath_assoc oneCellA1 oneCellB1 oneCellC1)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta) cellGamma)) := by
  -- The three matched columns.
  -- termOne  : whiskerRight (B0·C0) α          ≈ cast (whiskerRight C0 (whiskerRight B0 α))
  -- termTwo  : whiskerLeft A1 (whiskerRight C0 β) ≈ cast (whiskerRight C0 (whiskerLeft A1 β))
  -- termThree: whiskerLeft A1 (whiskerLeft B1 γ)  ≈ cast (whiskerLeft (A1·B1) γ)
  have haveOne :
      TwoCellConvFull signature
        (RawTwoCellExpr.whiskerRight (composePath oneCellB0 oneCellC0) cellAlpha)
        (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellA0 oneCellB0 oneCellC0)
          (composePath_assoc oneCellA1 oneCellB0 oneCellC0)
          (RawTwoCellExpr.whiskerRight oneCellC0 (RawTwoCellExpr.whiskerRight oneCellB0 cellAlpha))) :=
    TwoCellConvFull.whiskerRightComp oneCellB0 oneCellC0 cellAlpha
  have haveTwo :
      TwoCellConvFull signature
        (RawTwoCellExpr.whiskerLeft oneCellA1 (RawTwoCellExpr.whiskerRight oneCellC0 cellBeta))
        (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellA1 oneCellB0 oneCellC0)
          (composePath_assoc oneCellA1 oneCellB1 oneCellC0)
          (RawTwoCellExpr.whiskerRight oneCellC0 (RawTwoCellExpr.whiskerLeft oneCellA1 cellBeta))) :=
    TwoCellConvFull.whiskerExchange oneCellA1 oneCellC0 cellBeta
  have haveThree :
      TwoCellConvFull signature
        (RawTwoCellExpr.whiskerLeft oneCellA1 (RawTwoCellExpr.whiskerLeft oneCellB1 cellGamma))
        (RawTwoCellExpr.castBoundary
          (composePath_assoc oneCellA1 oneCellB1 oneCellC0)
          (composePath_assoc oneCellA1 oneCellB1 oneCellC1)
          (RawTwoCellExpr.whiskerLeft (composePath oneCellA1 oneCellB1) cellGamma)) := by
    have base := TwoCellConvFull.castBoundaryCongr
      (composePath_assoc oneCellA1 oneCellB1 oneCellC0)
      (composePath_assoc oneCellA1 oneCellB1 oneCellC1)
      (TwoCellConvFull.whiskerLeftComp oneCellA1 oneCellB1 cellGamma)
    rw [RawTwoCellExpr.castBoundary_castBoundary] at base
    exact TwoCellConvFull.symm base
  -- Distribute the left whisker over the inner vcomp (the LHS's right factor).
  refine TwoCellConvFull.trans
    (TwoCellConvFull.vcompCongrRight _
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerLeftVcomp oneCellA1
          (RawTwoCellExpr.whiskerRight oneCellC0 cellBeta)
          (RawTwoCellExpr.whiskerLeft oneCellB1 cellGamma))))) ?_
  -- Rewrite each of the three columns to its cast form.
  refine TwoCellConvFull.trans (TwoCellConvFull.vcompCongrLeft _ haveOne) ?_
  refine TwoCellConvFull.trans (TwoCellConvFull.vcompCongrRight _
    (TwoCellConvFull.vcompCongrLeft _ haveTwo)) ?_
  refine TwoCellConvFull.trans (TwoCellConvFull.vcompCongrRight _
    (TwoCellConvFull.vcompCongrRight _ haveThree)) ?_
  -- Fuse the per-column casts across the two vertical seams.
  rw [RawTwoCellExpr.vcomp_castBoundary_merge, RawTwoCellExpr.vcomp_castBoundary_merge]
  -- The consolidated inner cell is the RHS's uncast three-column composite; fold it back to `(α ⊠ β) ⊠ γ`.
  refine TwoCellConvFull.castBoundaryCongr _ _ (TwoCellConvFull.symm ?_)
  -- (α ⊠ β) ⊠ γ  ≈  S1 ⊟ (S2 ⊟ S3)  via whiskerRightVcomp then vcompAssoc.
  show TwoCellConvFull signature
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerRight oneCellC0
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellB0 cellAlpha)
          (RawTwoCellExpr.whiskerLeft oneCellA1 cellBeta)))
      (RawTwoCellExpr.whiskerLeft (composePath oneCellA1 oneCellB1) cellGamma))
    _
  refine TwoCellConvFull.trans
    (TwoCellConvFull.vcompCongrLeft _
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp oneCellC0
          (RawTwoCellExpr.whiskerRight oneCellB0 cellAlpha)
          (RawTwoCellExpr.whiskerLeft oneCellA1 cellBeta))))) ?_
  exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
    (TwoCellStep.vcompAssoc
      (RawTwoCellExpr.whiskerRight oneCellC0 (RawTwoCellExpr.whiskerRight oneCellB0 cellAlpha))
      (RawTwoCellExpr.whiskerRight oneCellC0 (RawTwoCellExpr.whiskerLeft oneCellA1 cellBeta))
      (RawTwoCellExpr.whiskerLeft (composePath oneCellA1 oneCellB1) cellGamma)))

/-! ## Right-factor congruence of the Godement product on the saturated relation -/

/-- Congruence in the RIGHT factor of a horizontal composite: replacing the right factor by a saturated-convertible
(parallel) one gives a saturated-convertible horizontal composite.  `hcomp α β = vcomp (whiskerRight β_dom α)
(whiskerLeft α_cod β)`; the left `whiskerRight` factor is unchanged (parallel `β` share a domain), the right
`whiskerLeft` factor threads the convertibility (`whiskerLeftCongr`). -/
theorem MonadSaturatedTwoCellConv.hcompCongrRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellFDom oneCellFCod : ModalityPath monadModeSignature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath monadModeSignature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellFDom oneCellFCod)
    {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellGDom oneCellGCod}
    (conv : MonadSaturatedTwoCellConv cellBeta cellBeta') :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha cellBeta') :=
  MonadSaturatedTwoCellConv.vcompCongrRight _
    (MonadSaturatedTwoCellConv.whiskerLeftCongr oneCellFCod conv)

/-! ## The codomain boundary of an appended word -/

/-- The codomain 1-cell of a cons-appended word is `t^(a.length) · t^(b.length)` — the ordinal sum of the two
sub-words' codomains. -/
theorem monadTPower_length_consAppend (a b : List Nat) :
    monadTPower (consAppend a b).length
      = composePath (monadTPower a.length) (monadTPower b.length) := by
  rw [consAppend_length]; exact monadTPower_add a.length b.length

/-! ## The HORIZONTAL word multiplicativity -/

/-- ★ **HORIZONTAL word multiplicativity.**  The canonical Eilenberg–Zilber word of a cons-APPENDED counts list is
the horizontal composite of the two sub-words (up to the domain / codomain associator cast): `word (a ++ b) ≈
cast ((word a) ⊠ (word b))`.  Structural induction on `a`:

  * `a = []` — `word ([] ++ b) = word b`; the RHS `hcomp (id t^0) (word b)` collapses by `whiskerRightId` +
    `vcompIdLeft` + `whiskerLeftUnit` and the boundary cast is definitionally the identity.
  * `a = c :: a'` — `word ((c :: a') ++ b) = hcomp (gadget c) (word (a' ++ b))`; the induction hypothesis splits
    `word (a' ++ b)` into `hcomp (word a') (word b)` under the head gadget (`hcompCongrRight`), the cast pulls out
    of the head gadget (`hcomp_castBoundaryRight`), and `hcompAssoc` re-brackets `gadget c ⊠ (word a' ⊠ word b)`
    to `(gadget c ⊠ word a') ⊠ word b = word (c :: a') ⊠ word b` (the head gadget re-absorbs into `word (c::a')`
    definitionally); the two casts fuse (`castBoundary_castBoundary`).

Pure free-2-category — no monad law. -/
theorem wordMul_hcomp : ∀ (a b : List Nat),
    MonadSaturatedTwoCellConv
      (wordFromCounts (consAppend a b))
      (RawTwoCellExpr.castBoundary
        (countsDomainPath_consAppend a b).symm
        (monadTPower_length_consAppend a b).symm
        (RawTwoCellExpr.hcomp (wordFromCounts a) (wordFromCounts b)))
  | [], b => by
      show MonadSaturatedTwoCellConv (wordFromCounts b)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))
          (wordFromCounts b))
      refine MonadSaturatedTwoCellConv.symm ?_
      show MonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath b)
            (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower 0) (wordFromCounts b)))
        (wordFromCounts b)
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft _
          (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightId (signature := monadModeSignature) (monadTPower 0) (countsDomainPath b))))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
          (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))) ?_
      exact MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (wordFromCounts b))
  | c :: a', b => by
      show MonadSaturatedTwoCellConv
        (RawTwoCellExpr.hcomp (monadGadget c) (wordFromCounts (consAppend a' b)))
        (RawTwoCellExpr.castBoundary
          (countsDomainPath_consAppend (c :: a') b).symm
          (monadTPower_length_consAppend (c :: a') b).symm
          (RawTwoCellExpr.hcomp (wordFromCounts (c :: a')) (wordFromCounts b)))
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.hcompCongrRight (monadGadget c) (wordMul_hcomp a' b)) ?_
      rw [RawTwoCellExpr.hcomp_castBoundaryRight]
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.castBoundaryCongr _ _
          (MonadSaturatedTwoCellConv.ofFull
            (hcompAssoc (monadGadget c) (wordFromCounts a') (wordFromCounts b)))) ?_
      have hfuse :
          RawTwoCellExpr.castBoundary
              (congrArg (composePath (monadTPower c)) (countsDomainPath_consAppend a' b).symm)
              (congrArg (composePath monadT) (monadTPower_length_consAppend a' b).symm)
              (RawTwoCellExpr.castBoundary
                (composePath_assoc (monadTPower c) (countsDomainPath a') (countsDomainPath b))
                (composePath_assoc monadT (monadTPower a'.length) (monadTPower b.length))
                (RawTwoCellExpr.hcomp
                  (RawTwoCellExpr.hcomp (monadGadget c) (wordFromCounts a')) (wordFromCounts b)))
            = RawTwoCellExpr.castBoundary
                (countsDomainPath_consAppend (c :: a') b).symm
                (monadTPower_length_consAppend (c :: a') b).symm
                (RawTwoCellExpr.hcomp (wordFromCounts (c :: a')) (wordFromCounts b)) := by
        rw [RawTwoCellExpr.castBoundary_castBoundary]; rfl
      exact hfuse ▸ MonadSaturatedTwoCellConv.refl _

end FX1Poly.Polygraph
