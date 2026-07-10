import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated


/-! # WalkingMonad/MonadWordMultGen — the whisker/horizontal WORD MULTIPLICATIVITY over the GENERIC carrier
(POLY-TAB r6 monad re-founding, WAVE 2, Brick A)

The completeness-leg port: the whisker + horizontal word-multiplicativity lemmas re-founded ctor-for-ctor over the
generic `SaturatedConvOver monadModeSignature MonadLawRel` carrier (the three bespoke law ctors fold into
`ofRelation` of a `MonadLawRel` row).  These leaves use ONLY free-strict-2-category laws — no monad law — so their
constant-closure contains NO `MonadSaturatedTwoCellConv`.  The carrier-only cast/data lemmas
(`consAppend`, `hcompAssoc`, the `RawTwoCellExpr.*` casts, `countsDomainPath_*`) are REUSED by reference.

Raw Lean 4 + Init; zero-axiom; STRUCTURAL.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-- Definitionally-equal cells are generically saturated-convertible (an `Eq` lifts to `SaturatedConvOver`).  The
generic twin of the bespoke `MonadSaturatedTwoCellConv.ofEq`, threading `castBoundary`-fusion equalities through the
congruences without a motive-fragile `rw`. -/
theorem SaturatedConvOver.ofEq {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (heq : cellAlpha = cellBeta) :
    SaturatedConvOver signature baseRel cellAlpha cellBeta := by
  cases heq; exact SaturatedConvOver.refl cellAlpha

/-- Congruence in the LEFT factor of a horizontal composite on the generic saturated relation (the generic twin of
`MonadSaturatedTwoCellConv.hcompCongrLeft`).  `hcomp a b = vcomp (whiskerRight b_dom a) (whiskerLeft a_cod b)`; the
right `whiskerLeft` factor is unchanged, the left `whiskerRight` factor threads the convertibility. -/
theorem SaturatedConvOver.hcompCongrLeft {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellFDom oneCellFCod}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellAlpha')
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    SaturatedConvOver signature baseRel (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha' cellBeta) :=
  SaturatedConvOver.vcompCongrLeft _ (SaturatedConvOver.whiskerRightCongr oneCellGDom conv)

/-- Congruence in the RIGHT factor of a horizontal composite on the generic saturated relation (the generic twin of
`MonadSaturatedTwoCellConv.hcompCongrRight`). -/
theorem SaturatedConvOver.hcompCongrRight {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellGDom oneCellGCod}
    (conv : SaturatedConvOver signature baseRel cellBeta cellBeta') :
    SaturatedConvOver signature baseRel (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha cellBeta') :=
  SaturatedConvOver.vcompCongrRight _ (SaturatedConvOver.whiskerLeftCongr oneCellFCod conv)

/-! ## The ones-word collapse, generic carrier (prerequisite for the RIGHT-whisker mult) -/

/-- The `count + 1` ones word peels its leading `id_t` gadget: `wordFromCounts (ones (count+1))` — a horizontal
composite `hcomp id_t (wordFromCounts (ones count))` — reduces to `t ◁ wordFromCounts (ones count)` by dropping the
right-whisker identity (`whiskerRightId`) and the left identity factor (`vcompIdLeft`).  Pure free-2-category, no
monad law. -/
theorem wordFromCounts_monadOnes_succ_convGen (count : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel (wordFromCounts (monadOnes (count + 1)))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count))) := by
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath (monadOnes count))
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count))))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft _
      (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT (countsDomainPath (monadOnes count)))))) ?_
  exact SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
    (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))

/-- ★ **The ones word collapses to the identity 2-cell** (transported to the word's native boundary).  Induction on
`count`: the base is the empty identity; the step peels the leading `id_t` gadget (`wordFromCounts_monadOnes_succ_convGen`),
applies the induction hypothesis under a left whisker (`whiskerLeftCongr`), pulls the cast out of the whisker
(`monadWhiskerLeft_castBoundary`), and collapses `t ◁ id` to `id` (`whiskerLeftId`).  Uses ONLY free-2-category
laws — no monad law. -/
theorem wordFromCounts_monadOnes_convGen : ∀ (count : Nat),
    SaturatedConvOver monadModeSignature MonadLawRel (wordFromCounts (monadOnes count))
      (RawTwoCellExpr.castBoundary (countsDomainPath_monadOnes count).symm
        (congrArg monadTPower (length_monadOnes count).symm)
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower count)))
  | 0 => SaturatedConvOver.refl (baseRel := MonadLawRel) _
  | count + 1 => by
      refine SaturatedConvOver.trans (wordFromCounts_monadOnes_succ_convGen count) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.whiskerLeftCongr monadT (wordFromCounts_monadOnes_convGen count)) ?_
      -- Pull the boundary cast out of the left whisker (a genuine propositional equality — `▸`, not `rw`, to dodge
      -- the dependent-index motive), then collapse `t ◁ id` to `id` under the same cast.
      have hpull := monadWhiskerLeft_castBoundary (countsDomainPath_monadOnes count).symm
        (congrArg monadTPower (length_monadOnes count).symm)
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower count))
      have hconv := SaturatedConvOver.castBoundaryCongr
        (congrArg (composePath monadT) (countsDomainPath_monadOnes count).symm)
        (congrArg (composePath monadT) (congrArg monadTPower (length_monadOnes count).symm))
        (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
          (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower count))))
      exact hpull.symm ▸ hconv

/-! ## LEFT-whisker word multiplicativity, generic carrier -/

/-- ★ **A leading `1` of a word is a left-`t`-whisker.**  `wordFromCounts (1 :: rest)` — a horizontal composite
`hcomp id_t (wordFromCounts rest)` — reduces to `t ◁ wordFromCounts rest` by dropping the right-whisker identity
(`whiskerRightId`) and the left identity factor (`vcompIdLeft`).  The `wordFromCounts_monadOnes_succ_convGen` pattern,
generalized to an arbitrary tail `rest`.  Pure free-2-category, no monad law. -/
theorem wordFromCounts_consOne_convGen (rest : List Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel (wordFromCounts (1 :: rest))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest)) := by
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest)))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft _
      (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT (countsDomainPath rest))))) ?_
  exact SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
    (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))

/-- ★ **LEFT-whisker word multiplicativity.**  Whiskering the canonical word of `counts` on the left by `t^k` is
saturated-convertible to the canonical word of the `k`-ones-PREFIXED counts (the `k` new strands each hit their own
fresh target once — the identity block).  Structural induction on `k`: `k = 0` is the unit-1-cell whisker
(`whiskerLeftUnit`); the `k + 1` step splits `t^(k+1) = t · t^k` (`whiskerLeftComp`), threads the induction
hypothesis under a `t`-whisker (`whiskerLeftCongr`, pulling the boundary cast out via `whiskerLeft_castBoundary` and
fusing via `castBoundary_castBoundary`), and re-folds the leading `1` (`wordFromCounts_consOne_convGen`).  The residual
boundary casts coincide by proof-irrelevance (same endpoints).  Pure free-2-category — no monad law. -/
theorem wordMul_whiskerLeftGen : ∀ (k : Nat) (counts : List Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k) (wordFromCounts counts))
      (RawTwoCellExpr.castBoundary (countsDomainPath_consReplicate_one k counts)
        (monadTPower_length_consReplicate_one k counts)
        (wordFromCounts (consReplicate 1 k counts)))
  | 0, counts => SaturatedConvOver.ofFull (baseRel := MonadLawRel) (TwoCellConvFull.whiskerLeftUnit (wordFromCounts counts))
  | k + 1, counts => by
      show SaturatedConvOver monadModeSignature MonadLawRel
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature)
          (composePath monadT (monadTPower k)) (wordFromCounts counts))
        (RawTwoCellExpr.castBoundary (countsDomainPath_consReplicate_one (k + 1) counts)
          (monadTPower_length_consReplicate_one (k + 1) counts)
          (wordFromCounts (consReplicate 1 (k + 1) counts)))
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofFull (baseRel := MonadLawRel)
          (TwoCellConvFull.whiskerLeftComp monadT (monadTPower k) (wordFromCounts counts))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (SaturatedConvOver.whiskerLeftCongr monadT (wordMul_whiskerLeftGen k counts))) ?_
      rw [monadWhiskerLeft_castBoundary]
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (SaturatedConvOver.castBoundaryCongr _ _
            (SaturatedConvOver.symm (wordFromCounts_consOne_convGen (consReplicate 1 k counts))))) ?_
      rw [monadCastBoundary_castBoundary]
      exact SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-! ## HORIZONTAL word multiplicativity, generic carrier -/

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
theorem wordMul_hcompGen : ∀ (a b : List Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (wordFromCounts (consAppend a b))
      (RawTwoCellExpr.castBoundary
        (countsDomainPath_consAppend a b).symm
        (monadTPower_length_consAppend a b).symm
        (RawTwoCellExpr.hcomp (wordFromCounts a) (wordFromCounts b)))
  | [], b => by
      show SaturatedConvOver monadModeSignature MonadLawRel (wordFromCounts b)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))
          (wordFromCounts b))
      refine SaturatedConvOver.symm ?_
      show SaturatedConvOver monadModeSignature MonadLawRel
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath b)
            (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower 0) (wordFromCounts b)))
        (wordFromCounts b)
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft _
          (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightId (signature := monadModeSignature) (monadTPower 0) (countsDomainPath b))))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
          (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))) ?_
      exact SaturatedConvOver.ofFull (baseRel := MonadLawRel) (TwoCellConvFull.whiskerLeftUnit (wordFromCounts b))
  | c :: a', b => by
      show SaturatedConvOver monadModeSignature MonadLawRel
        (RawTwoCellExpr.hcomp (monadGadget c) (wordFromCounts (consAppend a' b)))
        (RawTwoCellExpr.castBoundary
          (countsDomainPath_consAppend (c :: a') b).symm
          (monadTPower_length_consAppend (c :: a') b).symm
          (RawTwoCellExpr.hcomp (wordFromCounts (c :: a')) (wordFromCounts b)))
      refine SaturatedConvOver.trans
        (SaturatedConvOver.hcompCongrRight (monadGadget c) (wordMul_hcompGen a' b)) ?_
      rw [RawTwoCellExpr.hcomp_castBoundaryRight]
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _
          (SaturatedConvOver.ofFull (baseRel := MonadLawRel)
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
      exact hfuse ▸ SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-! ## RIGHT-whisker word multiplicativity, generic carrier -/

/-- ★ **RIGHT-whisker word multiplicativity.**  Whiskering the canonical word of `counts` on the RIGHT by `t^k` is
saturated-convertible to the canonical word of the `k`-ones-APPENDED counts (the `k` new strands each hit their own
fresh TOP target once — the identity block at the top of the vector).  Structural induction on `counts`:

  * `counts = []` — `t^k ▷ id (t^0) ≈ id (t^k)` (`whiskerRightId`), and the ones word `word (1^k)` collapses to
    `id (t^k)` (`wordFromCounts_monadOnes_convGen`), the boundary casts fusing.
  * `counts = c :: rest` — the head-gadget word `hcomp (gadget c) (word rest)` is right-whiskered: `whiskerRight_hcomp`
    distributes the `t^k` whisker into the RIGHT factor `word rest`, the induction hypothesis
    (`t^k ▷ word rest ≈ word (rest ++ 1^k)`) threads under the head gadget via the `hcomp`-right-congruence, and
    `hcomp_castBoundaryRight` + `castBoundary_castBoundary` pull the induction-hypothesis cast out of the head
    gadget and fuse it with the distributivity cast — landing exactly on `word (c :: (rest ++ 1^k)) =
    word ((c :: rest) ++ 1^k)`.

Pure free-2-category — no monad law.  The RIGHT dual of `wordMul_whiskerLeftGen`. -/
theorem wordMul_whiskerRightGen (k : Nat) : ∀ (counts : List Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (wordFromCounts counts))
      (RawTwoCellExpr.castBoundary (countsDomainPath_consAppend_ones counts k)
        (monadTPower_length_consAppend_ones counts k)
        (wordFromCounts (consAppend counts (monadOnes k))))
  | [] => by
      show SaturatedConvOver monadModeSignature MonadLawRel
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k)
            (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
          (RawTwoCellExpr.castBoundary (countsDomainPath_monadOnes k)
            (congrArg monadTPower (length_monadOnes k))
            (wordFromCounts (monadOnes k)))
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
          (TwoCellStep.whiskerRightId (signature := monadModeSignature) (monadTPower 0) (monadTPower k)))) ?_
      refine SaturatedConvOver.symm ?_
      have hstep := SaturatedConvOver.castBoundaryCongr
        (countsDomainPath_monadOnes k) (congrArg monadTPower (length_monadOnes k))
        (wordFromCounts_monadOnes_convGen k)
      rw [monadCastBoundary_castBoundary, monadCastBoundary_id] at hstep
      exact hstep
  | c :: rest => by
      show SaturatedConvOver monadModeSignature MonadLawRel
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k)
            (RawTwoCellExpr.hcomp (monadGadget c) (wordFromCounts rest)))
          _
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofFull (baseRel := MonadLawRel)
          (whiskerRight_hcomp (monadTPower k) (monadGadget c) (wordFromCounts rest))) ?_
      have hcompRightCongr : SaturatedConvOver monadModeSignature MonadLawRel
          (RawTwoCellExpr.hcomp (monadGadget c)
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (wordFromCounts rest)))
          (RawTwoCellExpr.hcomp (monadGadget c)
            (RawTwoCellExpr.castBoundary (countsDomainPath_consAppend_ones rest k)
              (monadTPower_length_consAppend_ones rest k)
              (wordFromCounts (consAppend rest (monadOnes k))))) :=
        SaturatedConvOver.vcompCongrRight _
          (SaturatedConvOver.whiskerLeftCongr monadT (wordMul_whiskerRightGen k rest))
      refine SaturatedConvOver.trans
        (SaturatedConvOver.castBoundaryCongr _ _ hcompRightCongr) ?_
      rw [RawTwoCellExpr.hcomp_castBoundaryRight, RawTwoCellExpr.castBoundary_castBoundary]
      exact SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-- **ESTABLISHED — the whisker + horizontal WORD MULTIPLICATIVITY are re-founded GENERIC-NATIVE.**  `wordMul_whiskerLeftGen`
/ `wordMul_whiskerRightGen` / `wordMul_hcompGen` over `SaturatedConvOver monadModeSignature MonadLawRel`, bespoke-free.
`= true`. -/
def fxMonad_hasWordMultGen : Bool := true

end FX1Poly.Polygraph.Amalgam
