import FX1Poly.Polygraph.Computad.Signature

/-! # WalkingBraid/BraidThreeSeed — the walking positive braid `B_3^+ = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩` signature + relation

The presentation of the WALKING (positive) BRAID on three strands as a mode theory: ONE mode `point`, TWO
endo-1-generators `σ1, σ2 : point ⟶ point` (the two elementary strand crossings), and the single **braid /
Yang–Baxter relation** `σ1.σ2.σ1 ≈ σ2.σ1.σ2` at the 1-CELL level.  There are NO generating 2-cells — the
2-signature is FREE ON NOTHING (`twoCell := fun _ _ => Empty`), so 2-cell equality is exactly 1-cell equality
and the whole word problem lives one dimension DOWN.

## Why `n = 3` — the minimal braid carrying a relation

`B_2^+ = ⟨σ1 | ⟩` is free on one generator (≅ ℕ, no relation — nothing to exhibit).  `B_3^+ = ⟨σ1, σ2 |
σ1σ2σ1 = σ2σ1σ2⟩` is the SMALLEST positive braid monoid carrying the braid move, so it is the minimal walker
that exhibits the Yang–Baxter content — mirroring the "walking" minimality philosophy of `WalkingCyclicThree`
(smallest `n` exhibiting `Z/n`).  The soundness target is the symmetric group `S_3` (six elements), the
underlying-permutation quotient.

## The one structural difference from cyclic-3 / involution

`WalkingCyclicThree`/`WalkingInvolution` have ONE endo-1-generator `s`; the braid has TWO (`σ1`, `σ2`).  Hence
the congruence generator `consCongr` here is GENERIC over any generator (not the single-`s` congruence of
cyclic-3): the front-firing `braidRel` whiskered by an arbitrary suffix, PLUS the generic `consCongr`, PLUS
`symm`/`trans`, generate the full two-sided monoid congruence — that is the correctness crux of this encoding.

## Boundary — NOT the Omega bunched-bimonoid braid

This is the clean `ModalityPath` 1-cell walker.  It is DELIBERATELY not coupled to the Omega
`bunchedBimonoidGenericBraidConv` (`FX1Poly/Polygraph/Omega/WalkingBunchedBimonoidGenericBraidConv.lean`),
which encodes the braid at the 2-cell level of a symmetric-monoidal matrix-PROP over a "star scope" — a
different, heavier presentation.  Cross-referenced here for orientation only.

## Scope — BRICK 1

This file ships the SIGNATURE + the braid relation as a 1-cell convertibility.  The underlying-permutation map
and the SOUNDNESS theorem (convertible braid words ⟹ equal permutation) live in `BraidThreePermutation`.  The
FULL braid-group word-problem DECISION needs Garside normal form and is WP-BRAID-2/3 — NOT attempted here.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The walking-braid quiver: one object, two endo-generators -/

/-- The single mode (0-cell) of the walking braid. -/
inductive BraidThreeMode where
  /-- The unique object. -/
  | point

/-- The TWO generating modalities (1-cells) of the walking braid: the elementary strand crossings
`σ1, σ2 : point ⟶ point`.  This is the one structural difference from the single-generator cyclic-3 /
involution walkers. -/
inductive BraidThreeModality : BraidThreeMode → BraidThreeMode → Type where
  /-- The first elementary crossing `σ1` (transposes strands 0 and 1). -/
  | sigma1 : BraidThreeModality BraidThreeMode.point BraidThreeMode.point
  /-- The second elementary crossing `σ2` (transposes strands 1 and 2). -/
  | sigma2 : BraidThreeModality BraidThreeMode.point BraidThreeMode.point

/-- The walking-braid quiver: one mode, two endo-modalities. -/
def braidThreeGraph : ModeGraph where
  Mode := BraidThreeMode
  Modality := BraidThreeModality

/-- The identity 1-cell at `point` (the empty word). -/
def braidThreeNil : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.nil (graph := braidThreeGraph) BraidThreeMode.point

/-- The generating crossing `σ1` as the length-1 free 1-cell (the single-step path). -/
def braidThreeSigma1 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  singletonModalityPath BraidThreeModality.sigma1

/-- The generating crossing `σ2` as the length-1 free 1-cell (the single-step path). -/
def braidThreeSigma2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  singletonModalityPath BraidThreeModality.sigma2

/-- The left-hand side of the braid relation: the length-3 word `σ1.σ2.σ1`. -/
def braidThreeBraidLeft : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma1
    (ModalityPath.cons BraidThreeModality.sigma2
      (ModalityPath.cons BraidThreeModality.sigma1 braidThreeNil))

/-- The right-hand side of the braid relation: the length-3 word `σ2.σ1.σ2`. -/
def braidThreeBraidRight : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma2
    (ModalityPath.cons BraidThreeModality.sigma1
      (ModalityPath.cons BraidThreeModality.sigma2 braidThreeNil))

/-- ★ The **walking-braid mode signature** — the degenerate 2-computad: the braid quiver with NO generating
2-cells (`twoCell` is `Empty` on every parallel pair).  The braid's only relation lives at the 1-cell level
(`σ1.σ2.σ1 = σ2.σ1.σ2`, the `BraidThreeOneCellConv` below); at the 2-cell level the signature is FREE ON
NOTHING, so 2-cell equality collapses to 1-cell equality. -/
def braidThreeModeSignature : ModeSignature where
  graph := braidThreeGraph
  twoCell := fun _ _ => Empty

/-! ## Freeness / degeneracy smokes -/

/-- Smoke: `σ1` is the length-1 1-cell. -/
theorem braidThreeSigma1_length : braidThreeSigma1.length = 1 := rfl

/-- Smoke: `σ2` is the length-1 1-cell. -/
theorem braidThreeSigma2_length : braidThreeSigma2.length = 1 := rfl

/-- Smoke: the braid relation's left-hand side `σ1.σ2.σ1` is the length-3 1-cell. -/
theorem braidThreeBraidLeft_length : braidThreeBraidLeft.length = 3 := rfl

/-- Smoke: the braid relation's right-hand side `σ2.σ1.σ2` is the length-3 1-cell (both sides equal length —
the braid move preserves word length). -/
theorem braidThreeBraidRight_length : braidThreeBraidRight.length = 3 := rfl

/-- Smoke: the 2-signature is FREE ON NOTHING — there is no generating 2-cell between any parallel pair (here
`σ1 ⇒ σ1`), so 2-cell equality is 1-cell equality. -/
theorem braidThree_no_two_generators
    (generatingTwoCell : braidThreeModeSignature.twoCell braidThreeSigma1 braidThreeSigma1) : False :=
  nomatch generatingTwoCell

/-! ## The braid `σ1.σ2.σ1 = σ2.σ1.σ2` 1-cell convertibility -/

/-- ★ The **braid 1-cell convertibility** of the walking braid `B_3^+` — the free-1-category convertibility of
the braid quiver plus the single braid law `σ1.σ2.σ1 ≈ σ2.σ1.σ2`, closed under the GENERIC `cons`-congruence and
`refl`/`symm`/`trans` into a genuine congruence.  Two words are equal AS 1-cells of `B_3^+` exactly when they
are `BraidThreeOneCellConv`-related.  Because there are TWO generating 1-cells, the congruence generator must
range over EITHER leading generator: the front-firing `braidRel` plus the generic `consCongr` plus `symm`/`trans`
generate the full two-sided congruence. -/
inductive BraidThreeOneCellConv :
    ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point →
    ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point → Prop where
  /-- The **braid / Yang–Baxter relation** `σ1.σ2.σ1 ≈ σ2.σ1.σ2`, whiskered on the right by an arbitrary suffix
  `rest`: `σ1.(σ2.(σ1.rest)) ≈ σ2.(σ1.(σ2.rest))`. -/
  | braidRel (rest : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
      BraidThreeOneCellConv
        (ModalityPath.cons BraidThreeModality.sigma1
          (ModalityPath.cons BraidThreeModality.sigma2
            (ModalityPath.cons BraidThreeModality.sigma1 rest)))
        (ModalityPath.cons BraidThreeModality.sigma2
          (ModalityPath.cons BraidThreeModality.sigma1
            (ModalityPath.cons BraidThreeModality.sigma2 rest)))
  /-- Congruence under a leading generator — GENERIC over either `σ1` or `σ2` (the two 1-cell contexts):
  `word1 ≈ word2 ⟹ gen.word1 ≈ gen.word2`.  This genericity (vs cyclic-3's single-`s` congruence) is what makes
  the front-firing `braidRel` generate the full two-sided monoid congruence. -/
  | consCongr {generator : BraidThreeModality BraidThreeMode.point BraidThreeMode.point}
      {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point} :
      BraidThreeOneCellConv word1 word2 →
      BraidThreeOneCellConv (ModalityPath.cons generator word1)
        (ModalityPath.cons generator word2)
  /-- Reflexivity. -/
  | refl (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
      BraidThreeOneCellConv word word
  /-- Symmetry. -/
  | symm {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point} :
      BraidThreeOneCellConv word1 word2 → BraidThreeOneCellConv word2 word1
  /-- Transitivity. -/
  | trans {word1 word2 word3 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point} :
      BraidThreeOneCellConv word1 word2 → BraidThreeOneCellConv word2 word3 →
      BraidThreeOneCellConv word1 word3

/-- ★ **The braid law holds** — `σ1.σ2.σ1 ≈ σ2.σ1.σ2` (at the empty suffix): the Yang–Baxter move. -/
theorem braidThreeLawHolds :
    BraidThreeOneCellConv braidThreeBraidLeft braidThreeBraidRight :=
  BraidThreeOneCellConv.braidRel braidThreeNil

/-- Smoke: the braid law fires UNDER a leading `σ1` — `σ1.(σ1.σ2.σ1) ≈ σ1.(σ2.σ1.σ2)` — exercising the generic
`cons`-congruence with the law generator (the whiskered braid law). -/
theorem braidThreeLawWhiskeredHolds :
    BraidThreeOneCellConv
      (ModalityPath.cons BraidThreeModality.sigma1 braidThreeBraidLeft)
      (ModalityPath.cons BraidThreeModality.sigma1 braidThreeBraidRight) :=
  BraidThreeOneCellConv.consCongr braidThreeLawHolds

end FX1Poly.Polygraph
