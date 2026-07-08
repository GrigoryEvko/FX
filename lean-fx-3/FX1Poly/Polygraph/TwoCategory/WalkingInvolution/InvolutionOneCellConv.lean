import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionSeed

/-! # WalkingInvolution/InvolutionOneCellConv — the `s.s = id` 1-cell convertibility

The walking involution's only relation is `s.s = id` at the 1-CELL level.  This file ships that relation as the
1-cell CONVERTIBILITY `InvolutionOneCellConv` — the free-1-category convertibility of the involution quiver
augmented with the single involution law, closed under the `cons`-congruence and `refl`/`symm`/`trans` into a
genuine congruence.  It is the sibling of the walking monad's saturated 2-cell relation
(`MonadSaturatedTwoCellConv`), ONE DIMENSION DOWN: where the monad saturates 2-cells over parallel 1-cells, the
involution saturates 1-cells over the single 0-cell `point`.

Because there is exactly ONE generating 1-cell `s`, the only context is `cons s _`, so the involution law `ssId`
(firing at the FRONT of a word) plus the `cons`-congruence plus `symm`/`trans` generate the full two-sided
congruence: `s^5 ≈ s^3` is `consCongr` twice around `ssId`, and `s^3 ≈ s` is `ssId` under a `consCongr`.

Raw Lean 4 + Init; the relation is an inductive `Prop`, so every declaration here is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- ★ The **`s.s = id` 1-cell convertibility** of the walking involution — the free-1-category convertibility of
the involution quiver plus the single involution law `s.s ≈ id`, closed under the `cons`-congruence and
`refl`/`symm`/`trans` into a genuine congruence.  Two words in `s` are equal AS 1-cells of the walking involution
(the terminal involution `⟨s | s.s = id⟩`) exactly when they are `InvolutionOneCellConv`-related.  All 1-cells are
endo at `point`, so the relation is over `ModalityPath involutionGraph point point`. -/
inductive InvolutionOneCellConv :
    ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point →
    ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point → Prop where
  /-- The **involution law** `s.s ≈ id`, whiskered on the right by an arbitrary suffix `rest`:
  `s.(s.rest) ≈ rest` (a double `s` at the front cancels). -/
  | ssId (rest : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
      InvolutionOneCellConv
        (ModalityPath.cons InvolutionModality.s (ModalityPath.cons InvolutionModality.s rest)) rest
  /-- Congruence under a leading `s` (the only 1-cell context): `word1 ≈ word2 ⟹ s.word1 ≈ s.word2`. -/
  | consCongr {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point} :
      InvolutionOneCellConv word1 word2 →
      InvolutionOneCellConv (ModalityPath.cons InvolutionModality.s word1)
        (ModalityPath.cons InvolutionModality.s word2)
  /-- Reflexivity. -/
  | refl (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
      InvolutionOneCellConv word word
  /-- Symmetry. -/
  | symm {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point} :
      InvolutionOneCellConv word1 word2 → InvolutionOneCellConv word2 word1
  /-- Transitivity. -/
  | trans {word1 word2 word3 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point} :
      InvolutionOneCellConv word1 word2 → InvolutionOneCellConv word2 word3 →
      InvolutionOneCellConv word1 word3

/-! ## The involution law witnesses (the presentation content) -/

/-- ★ **The involution law holds** — `s.s ≈ id` (at the empty suffix): the double dual cancels to the identity. -/
theorem involutionLawHolds :
    InvolutionOneCellConv
      (ModalityPath.cons InvolutionModality.s involutionS)
      (involutionNil) :=
  InvolutionOneCellConv.ssId (involutionNil)

/-- Smoke: `s.s.s ≈ s` — three duals reduce to one, by the involution law under NO context (fires at the front). -/
theorem involutionTripleReducesToSingle :
    InvolutionOneCellConv
      (ModalityPath.cons InvolutionModality.s (ModalityPath.cons InvolutionModality.s involutionS))
      involutionS :=
  InvolutionOneCellConv.ssId involutionS

/-- Smoke: the involution law fires UNDER a leading `s` — `s.(s.s) ≈ s.id = s` — exercising the `cons`-congruence
with the law generator (a genuine congruence, the whiskered involution law). -/
theorem involutionLawWhiskeredHolds :
    InvolutionOneCellConv
      (ModalityPath.cons InvolutionModality.s (ModalityPath.cons InvolutionModality.s involutionS))
      (ModalityPath.cons InvolutionModality.s (involutionNil)) :=
  InvolutionOneCellConv.consCongr involutionLawHolds

end FX1Poly.Polygraph
