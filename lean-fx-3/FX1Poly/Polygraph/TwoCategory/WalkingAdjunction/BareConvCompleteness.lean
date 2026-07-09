import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvGoldilocks

/-! # mode-3 floor — the bare-`TwoCellConv` COMPLETENESS frontier: the three-moment family is INCOMPLETE over
COMPOSITES, refuted by a genuine composite separating pair, and the family provably GROWS (the moment tower)

`BareConvGoldilocks` (r1) shipped the sound, decidable OVER-approximation `bareConvCandidate` (faithful
`TwoCellConvFull` PLUS equal `whiskerSum` / `rSum` / `crossSum`) and left ONE frontier genuinely open: its
COMPLETENESS (`candidate ⟹ bare`).  r1's honest wall was that the family catches every SINGLE
whisker-functoriality generating law (four by `whiskerSum` count, `whiskerExchange` by the `crossSum` order
moment) but "no separating pair for the FULL family is exhibited (that would name a needed FOURTH invariant), nor
is the family proven complete".

This file CLOSES that exact open — NOT by proving completeness (it is FALSE for the three-moment family), but by
EXHIBITING the missing composite separating pair and NAMING the fourth invariant.  MACHINE-CHECKED: the
three-moment `bareConvCandidate` is INCOMPLETE over COMPOSITES, and the fourth invariant `nestedCrossSum` is a
GENUINE, full-conv-VARIANT bare invariant (so the family provably does not collapse at three).  CHARACTERISED
(structural, §2 below — the reason, not separately mechanised): the complete bare invariant is the per-generator
pattern MULTISET, so every FINITE bounded-subsequence-moment tuple is a lossy shadow (an ascending tower).  This
is the honest deeper wall behind `fxMode_hasModeRelativeConvDecision` staying `false`.

## The structural reason ANY additive whisker-pattern moment is a bare invariant

Every bare `TwoCellStep` — INCLUDING interchange — preserves each generator's unlabelled `{L, R}` whisker-pattern
EXACTLY (interchange prepends the SAME letter at the SAME outer depth to every generator of each factor; the four
structural laws reshuffle vcomp / distribute a whisker to every generator identically; identity removal drops a
`0`-generator factor).  Consequently EVERY additive pattern-moment `Σ_gen φ(pattern(gen))` — for ANY
`φ : {L,R}* → ℕ` — is a bare-conv invariant.  The genuinely COMPLETE bare-invariant is the whole per-generator
unlabelled-pattern MULTISET; `(whiskerSum, rSum, crossSum)` is a lossy three-number shadow (length, `#R`,
`#(L-before-R)`), and any FINITE tuple of bounded-subsequence-length moments is likewise lossy.  This is the
Araújo-style pattern normal form specialised to a single generator; the OPEN converse (full-conv + equal
pattern-multiset ⟹ bare) is the interchange critical-pair coherence (Gratzer), untouched here.

## What this file ships (each piece zero-axiom)

  ★ **The five whisker-functoriality DEFECT vectors** — how each of the five laws (`whiskerLeftUnit`,
    `whiskerRightUnit`, `whiskerLeftComp`, `whiskerRightComp`, `whiskerExchange`) MOVES the moment tuple, as `rfl`
    equations on the law's LHS versus its (cast-invisible) RHS core.  `whiskerExchange` is the ONLY law with
    `Δwhisker = Δr = 0` — it moves `crossSum` alone (by `−generatorCount`), which is exactly why `crossSum` is the
    order separator.  `whiskerLeftComp` / `whiskerRightComp` are the exact inverses of `whiskerLeftUnit` /
    `whiskerRightUnit` on the tuple.
  ★ **`RawTwoCellExpr.leftCount` / `.coCrossSum` / `.nestedCrossSum`** — three further bare-conv moments.
    `leftCount = #L` (the mirror of `rSum`); `coCrossSum = #(R-before-L)` (the mirror of `crossSum`);
    `nestedCrossSum = #(L-before-R-before-L)` — the FOURTH invariant, a length-3 subsequence count `crossSum`
    cannot see.  All full-enum, constant-`Nat` motive, propext-free.
  ★ **`TwoCellConv.leftCount_eq` / `.coCrossSum_eq` / `.nestedCrossSum_eq`** — all three are GENUINE BARE-conv
    invariants, preserved by every `TwoCellStep` INCLUDING interchange (the make-or-break Godement critical pair,
    discharged by the same six-atom `Nat.add` reassociations `crossSum` used — `leftCount` mirrors `rSum`,
    `coCrossSum` mirrors `crossSum`, `nestedCrossSum` threads `coCrossSum`).
  ★ **`cellLRRL` / `cellRLLR`** — the COMPOSITE separating pair: single-generator pure-whisker chains with
    whisker words `L R R L` and `R L L R` (all identity-1-cell whiskers, so their boundaries coincide
    definitionally — NO boundary cast).  BOTH are `TwoCellConvFull` (a two-step `whiskerExchange` chain, cast-free
    at nil whiskers), agree on ALL THREE moments (`whiskerSum = 4`, `rSum = 2`, `crossSum = 2`), yet differ on
    `nestedCrossSum` (`2 ≠ 0`) — hence NOT bare `TwoCellConv`.
  ★ **`bareConvCandidate_not_complete_composite`** — the three-moment candidate `bareConvCandidate` HOLDS on the
    `cellLRRL` / `cellRLLR` pair yet the pair is NOT bare `TwoCellConv`: the candidate OVER-accepts a genuine
    COMPOSITE pair, so it is INCOMPLETE.  This is the full-family separating pair r1 left open.
  ★ **`bareConvCandidate4`** (adds `nestedCrossSum`) with soundness (`bareConvCandidate4_of_twoCellConv`),
    decidability (`adjunctionDecideBareConvCandidate4`), the exclusion of the `cellLRRL` / `cellRLLR` pair
    (`bareConvCandidate4_excludes_cellLRRL_cellRLLR`), and non-vacuity (accepts the genuine bare Eckmann–Hilton
    pair).  The fourth invariant STRICTLY refines the candidate — and is itself full-conv-VARIANT (a hallmark of a
    real separating invariant), so the family genuinely grows past three (the structural §2 tower argument
    extends it further, un-mechanised).

## What stays DEFERRED — `fxMode_hasModeRelativeConvDecision` NOT flipped

Completeness of NO finite moment family is established (the pattern-multiset is the true invariant, and each
finite tuple is refuted by a longer composite); bare `TwoCellConv`'s decidability stays the GENUINELY OPEN
interchange critical-pair coherence.  `fxMode_hasBareConvMomentFamilyProvablyLossy` records the strengthened
characterisation: the bounded-moment family is provably incomplete / an ascending tower.  `fxMode_...ConvDecision`
is NOT flipped and NOT touched; r1's soundness / statements are NOT weakened; the disposed trace / nfCell carriers
are NOT re-flipped; the saturated / faithful decisions are untouched.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
moments are constant-`Nat`-motive full-enum matches; the `_eq` lemmas are `induction` + explicit `Nat.add_*`
rewrites — never `omega`/`simp`/`ac_rfl`; the composite pair's full-conv is a cast-free `whiskerExchange` chain at
nil whiskers, the assoc casts collapsing by definitional proof irrelevance; the refutation is `Nat.noConfusion` on
`2 = 0`).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The three further bare-conv moments -/

/-- The **left-whisker incidence sum** `#L` — Σ over generators of the number of LEFT whiskers in its whisker
word.  The mirror of `rSum`: a LEFT whisker adds one incidence per generator in its body (`+ generatorCount`); a
RIGHT whisker passes through.  Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.leftCount {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.leftCount + cellBeta.leftCount
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.leftCount + cellBeta.generatorCount
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.leftCount

/-- The **right-outside-left crossing sum** `#(R-before-L)` — the mirror of `crossSum`.  A RIGHT whisker adds one
crossing per LEFT whisker already under it (`+ leftCount body`); a LEFT whisker passes through.  Full five-case
match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.coCrossSum {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.coCrossSum + cellBeta.coCrossSum
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.coCrossSum
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.coCrossSum + cellBeta.leftCount

/-- ★ The **nested crossing sum** `#(L-before-R-before-L)` — Σ over generators of the number of length-3 `L R L`
subsequences in its whisker word.  The FOURTH invariant, a length-3 subsequence count the length-2 `crossSum`
cannot see: a new OUTER left whisker becomes the leading `L` of an `L R L` with every `(R, L)` inversion already
in the body (`+ coCrossSum body`); a new outer RIGHT whisker cannot lead an `L R L` (`+ 0`).  Full five-case
match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.nestedCrossSum {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.nestedCrossSum + cellBeta.nestedCrossSum
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.nestedCrossSum + cellBeta.coCrossSum
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.nestedCrossSum

/-! ## `Nat` reassociation shapes for the interchange rebracketing -/

/-- Middle-four exchange for `Nat` addition — the shape whisker distribution takes on the degree-2/3 moments.
Propext-free (`Nat.add_assoc` / `Nat.add_left_comm`). -/
private theorem nat_add_middle_four_bcc (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm second third fourth]

/-- Six-term reassociation of the `nat_add_shuffle_six_r` shape (both Godement orders sum the same six atoms) —
the `coCrossSum` interchange rebracketing.  Two fully-instantiated middle-four exchanges, propext-free. -/
private theorem nat_add_shuffle_six_r_bcc (a b c d e f : Nat) :
    ((a + b) + (c + d)) + (e + f) = ((a + c) + e) + ((b + d) + f) := by
  rw [nat_add_middle_four_bcc a b c d, nat_add_middle_four_bcc (a + c) (b + d) e f]

/-- Six-term reassociation of the `nat_add_shuffle_six_cross` shape — the `leftCount` and `nestedCrossSum`
interchange rebracketings.  Two fully-instantiated middle-four exchanges, propext-free. -/
private theorem nat_add_shuffle_six_cross_bcc (a b c d e f : Nat) :
    (a + b) + ((c + d) + (e + f)) = (a + (c + e)) + (b + (d + f)) := by
  rw [nat_add_middle_four_bcc c d e f, nat_add_middle_four_bcc a b (c + e) (d + f)]

/-! ## `leftCount` is a bare-conv invariant (the mirror of `rSum`) -/

/-- ★ **`leftCount` is invariant under one 3-cell rewrite — INCLUDING interchange.**  The exact mirror of
`TwoCellStep.rSum_eq`: LEFT whiskering adds `generatorCount` (its congruence threads
`TwoCellStep.generatorCount_eq`); RIGHT whiskering passes through; interchange rebrackets the six atoms
`(leftCount α, leftCount α', leftCount β, leftCount β', generatorCount β, generatorCount β')`. -/
theorem TwoCellStep.leftCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.leftCount = reduct.leftCount := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.leftCount
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.leftCount cellBeta.leftCount cellGamma.leftCount
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.leftCount, RawTwoCellExpr.generatorCount]
      exact nat_add_middle_four_bcc cellBeta.leftCount cellGamma.leftCount
        cellBeta.generatorCount cellGamma.generatorCount
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.leftCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.leftCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.leftCount]
      rw [inductionHypothesis, subStep.generatorCount_eq]
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.leftCount, RawTwoCellExpr.generatorCount]
      exact nat_add_shuffle_six_cross_bcc
        cellAlpha.leftCount cellAlphaUpper.leftCount
        cellBeta.leftCount cellBetaUpper.leftCount
        cellBeta.generatorCount cellBetaUpper.generatorCount

/-- **`leftCount` is invariant under 2-cell convertibility.** -/
theorem TwoCellConv.leftCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.leftCount = reduct.leftCount := by
  induction conv with
  | ofStep step => exact step.leftCount_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## `coCrossSum` is a bare-conv invariant (the mirror of `crossSum`) -/

/-- ★ **`coCrossSum` is invariant under one 3-cell rewrite — INCLUDING interchange.**  The exact mirror of
`TwoCellStep.crossSum_eq`: RIGHT whiskering adds `leftCount` (its congruence threads `TwoCellStep.leftCount_eq`);
LEFT whiskering passes through; interchange rebrackets the six atoms
`(coCrossSum α, coCrossSum α', leftCount α, leftCount α', coCrossSum β, coCrossSum β')`. -/
theorem TwoCellStep.coCrossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.coCrossSum = reduct.coCrossSum := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.coCrossSum
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.coCrossSum cellBeta.coCrossSum cellGamma.coCrossSum
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ cellAlpha cellBeta =>
      dsimp only [RawTwoCellExpr.coCrossSum, RawTwoCellExpr.leftCount]
      exact nat_add_middle_four_bcc cellAlpha.coCrossSum cellBeta.coCrossSum
        cellAlpha.leftCount cellBeta.leftCount
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.coCrossSum]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.coCrossSum]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.coCrossSum]
      rw [inductionHypothesis, subStep.leftCount_eq]
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.coCrossSum, RawTwoCellExpr.leftCount]
      exact nat_add_shuffle_six_r_bcc
        cellAlpha.coCrossSum cellAlphaUpper.coCrossSum
        cellAlpha.leftCount cellAlphaUpper.leftCount
        cellBeta.coCrossSum cellBetaUpper.coCrossSum

/-- **`coCrossSum` is invariant under 2-cell convertibility.** -/
theorem TwoCellConv.coCrossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.coCrossSum = reduct.coCrossSum := by
  induction conv with
  | ofStep step => exact step.coCrossSum_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## `nestedCrossSum` is a bare-conv invariant (the FOURTH invariant) -/

/-- ★★ **`nestedCrossSum` is invariant under one 3-cell rewrite — INCLUDING interchange.**  LEFT whiskering adds
`coCrossSum` (its congruence threads `TwoCellStep.coCrossSum_eq`); RIGHT whiskering passes through; interchange
rebrackets the six atoms `(nestedCrossSum α, nestedCrossSum α', nestedCrossSum β, nestedCrossSum β',
coCrossSum β, coCrossSum β')` by the same `nat_add_shuffle_six_cross` shape.  This is the FOURTH bare-conv
invariant, surviving interchange, that the length-2 `crossSum` cannot supply. -/
theorem TwoCellStep.nestedCrossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.nestedCrossSum = reduct.nestedCrossSum := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.nestedCrossSum
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.nestedCrossSum cellBeta.nestedCrossSum cellGamma.nestedCrossSum
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.nestedCrossSum, RawTwoCellExpr.coCrossSum]
      exact nat_add_middle_four_bcc cellBeta.nestedCrossSum cellGamma.nestedCrossSum
        cellBeta.coCrossSum cellGamma.coCrossSum
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.nestedCrossSum]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.nestedCrossSum]; rw [inductionHypothesis]
  | whiskerLeftCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.nestedCrossSum]
      rw [inductionHypothesis, subStep.coCrossSum_eq]
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.nestedCrossSum, RawTwoCellExpr.coCrossSum]
      exact nat_add_shuffle_six_cross_bcc
        cellAlpha.nestedCrossSum cellAlphaUpper.nestedCrossSum
        cellBeta.nestedCrossSum cellBetaUpper.nestedCrossSum
        cellBeta.coCrossSum cellBetaUpper.coCrossSum

/-- **`nestedCrossSum` is invariant under 2-cell convertibility.**  A genuine BARE-conv invariant surviving
interchange, the fourth moment beyond the whisker-blind `generatorCount`, the order-blind `whiskerSum`, and the
length-2 `crossSum`. -/
theorem TwoCellConv.nestedCrossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.nestedCrossSum = reduct.nestedCrossSum := by
  induction conv with
  | ofStep step => exact step.nestedCrossSum_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## The five whisker-functoriality DEFECT vectors

For each of the five whisker-functoriality laws, the moment tuple `(whiskerSum, rSum, crossSum)` on the law's
LHS in terms of the RHS-core body.  The RHS is (four of five) a boundary cast; casting is moment-invisible
(`castBoundary` is `Eq.rec`, so `cases hsource; cases htarget; rfl`), so these LHS-vs-body equations ARE the
defect.  All are `rfl` (the moment recursions applied at one whisker node). -/

/-- Casting is invisible to `whiskerSum` (the moment output type depends only on the boundary MODES). -/
theorem RawTwoCellExpr.castBoundary_whiskerSum {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).whiskerSum = cell.whiskerSum := by
  cases hsource; cases htarget; rfl

/-- Casting is invisible to `rSum`. -/
theorem RawTwoCellExpr.castBoundary_rSum {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).rSum = cell.rSum := by
  cases hsource; cases htarget; rfl

/-- Casting is invisible to `crossSum`. -/
theorem RawTwoCellExpr.castBoundary_crossSum {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).crossSum = cell.crossSum := by
  cases hsource; cases htarget; rfl

/-- **Defect vector — `whiskerLeftUnit` (`identityPath ◁ body ≈ body`).**  `Δwhisker = +generatorCount`,
`Δr = 0`, `Δcross = +rSum` on the LHS over the body: reading the law left-to-right (LHS → body) the tuple moves
by `(−generatorCount, 0, −rSum)`. -/
theorem whiskerLeftUnit_defect {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body).whiskerSum
        = body.whiskerSum + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body).rSum = body.rSum
      ∧ (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body).crossSum
          = body.crossSum + body.rSum :=
  ⟨rfl, rfl, rfl⟩

/-- **Defect vector — `whiskerRightUnit` (`body ▷ identityPath ≈ cast body`).**  `Δwhisker = +generatorCount`,
`Δr = +generatorCount`, `Δcross = 0` on the LHS over the (cast-invisible) body: reading left-to-right the tuple
moves by `(−generatorCount, −generatorCount, 0)`. -/
theorem whiskerRightUnit_defect {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    (RawTwoCellExpr.whiskerRight (identityPath targetMode) body).whiskerSum
        = body.whiskerSum + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerRight (identityPath targetMode) body).rSum
          = body.rSum + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerRight (identityPath targetMode) body).crossSum = body.crossSum :=
  ⟨rfl, rfl, rfl⟩

/-- **Defect vector — `whiskerLeftComp` (`(outer ∘ inner) ◁ body ≈ cast (outer ◁ (inner ◁ body))`).**
`whiskerLeftComp` is the exact inverse of `whiskerLeftUnit`: splitting a composite whisker into two single
whiskers (the RHS-core `outer ◁ (inner ◁ body)`, one MORE node than the single-composite LHS) adds
`+generatorCount` to `whiskerSum` and `+rSum` to `crossSum`, exactly recovering what `whiskerLeftUnit` removes;
`rSum` unchanged. -/
theorem whiskerLeftComp_defect {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    (oneCellOuter : ModalityPath signature.graph sourceMode middleModeOne)
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    {oneCellDom oneCellCod : ModalityPath signature.graph middleModeTwo targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).whiskerSum
        = (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body).whiskerSum
          + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).rSum
          = (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body).rSum
      ∧ (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).crossSum
          = (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body).crossSum
            + body.rSum :=
  ⟨rfl, rfl, rfl⟩

/-- **Defect vector — `whiskerRightComp` (`(inner ∘ outer) ▷ body ≈ cast (outer ▷ (inner ▷ body))`).**  The
right dual: the split RHS-core `outer ▷ (inner ▷ body)` (one MORE node than the single-composite LHS) moves
`whiskerSum` by `+generatorCount` and `rSum` by `+generatorCount`, `crossSum` unchanged — the exact inverse of
`whiskerRightUnit`. -/
theorem whiskerRightComp_defect {signature : ModeSignature}
    {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
    (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
    (oneCellOuter : ModalityPath signature.graph middleModeTwo targetMode)
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleModeOne}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).whiskerSum
        = (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body).whiskerSum
          + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).rSum
          = (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body).rSum
            + body.generatorCount
      ∧ (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).crossSum
          = (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body).crossSum :=
  ⟨rfl, rfl, rfl⟩

/-- ★ **Defect vector — `whiskerExchange` (`left ◁ (body ▷ right) ≈ cast (right ▷ (left ◁ body))`).**  The ONLY
law with `Δwhisker = Δr = 0`: it moves `crossSum` ALONE — the LHS `left ◁ (body ▷ right)` (outer L over inner R,
one L-before-R crossing per generator) has `crossSum` EXACTLY `generatorCount body` MORE than the RHS-core
`right ▷ (left ◁ body)` (outer R over inner L, no such crossing).  This is precisely why `crossSum` is the order
separator that `whiskerSum` / `rSum` cannot supply. -/
theorem whiskerExchange_defect {signature : ModeSignature}
    {sourceMode middleSourceMode middleTargetMode targetMode : signature.graph.Mode}
    (leftWhisker : ModalityPath signature.graph sourceMode middleSourceMode)
    {bodyDom bodyCod : ModalityPath signature.graph middleSourceMode middleTargetMode}
    (rightWhisker : ModalityPath signature.graph middleTargetMode targetMode)
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).whiskerSum
        = (RawTwoCellExpr.whiskerRight rightWhisker
            (RawTwoCellExpr.whiskerLeft leftWhisker body)).whiskerSum
      ∧ (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).rSum
          = (RawTwoCellExpr.whiskerRight rightWhisker
              (RawTwoCellExpr.whiskerLeft leftWhisker body)).rSum
      ∧ (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).crossSum
          = (RawTwoCellExpr.whiskerRight rightWhisker
              (RawTwoCellExpr.whiskerLeft leftWhisker body)).crossSum + body.generatorCount :=
  ⟨rfl, rfl, (Nat.add_assoc body.crossSum body.rSum body.generatorCount).symm⟩

/-! ## The composite separating pair: `L R R L` versus `R L L R` -/

/-- The composite separating pair, LEFT member — whisker word `L R R L` (outer→inner) over the unit generator,
all whiskers the identity 1-cell.  Moments `(whiskerSum, rSum, crossSum) = (4, 2, 2)`, `nestedCrossSum = 2`. -/
abbrev cellLRRL :=
  RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      (RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          adjunctionUnitTwoCell)))

/-- The composite separating pair, RIGHT member — whisker word `R L L R` (outer→inner) over the unit generator,
all whiskers the identity 1-cell.  Its boundary coincides DEFINITIONALLY with `cellLRRL`'s (both dom
`composePath (composePath nil nil) nil`, both cod `composePath (composePath adjunctionLeftThenRight nil) nil`), so
the pair is statable with NO boundary cast.  Moments `(4, 2, 2)`, `nestedCrossSum = 0`. -/
abbrev cellRLLR :=
  RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        (RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          adjunctionUnitTwoCell)))

/-- The cast-free disjoint-whisker exchange at NIL whiskers: `nil ◁ (nil ▷ body) ≈full nil ▷ (nil ◁ body)`.  The
`whiskerExchange` constructor's associativity casts `composePath_assoc nil _ nil` are reflexive-typed (both sides
definitionally `composePath _ nil`), so by definitional proof irrelevance `castBoundary` collapses to the
identity and the constructor lands on the cast-free right-hand side. -/
theorem nilWhiskerExchange {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerLeft (identityPath sourceMode)
        (RawTwoCellExpr.whiskerRight (identityPath targetMode) body))
      (RawTwoCellExpr.whiskerRight (identityPath targetMode)
        (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body)) :=
  TwoCellConvFull.whiskerExchange (identityPath sourceMode) (identityPath targetMode) body

/-- ★ **The composite pair is `TwoCellConvFull`.**  A two-step cast-free `whiskerExchange` chain through the
intermediate `R L R L`: the outer `nil ◁ (nil ▷ _)` exchanges (`cellLRRL → RLRL`), then the innermost
`nil ◁ (nil ▷ unit)` reverse-exchanges under the fixed outer `nil ▷ (nil ◁ _)` prefix (`RLRL → cellRLLR`). -/
theorem cellLRRL_convFull_cellRLLR :
    TwoCellConvFull adjunctionModeSignature cellLRRL cellRLLR :=
  TwoCellConvFull.trans
    (nilWhiskerExchange (RawTwoCellExpr.whiskerRight
      (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        adjunctionUnitTwoCell)))
    (TwoCellConvFull.whiskerRightCongr (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      (TwoCellConvFull.whiskerLeftCongr (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        (nilWhiskerExchange adjunctionUnitTwoCell).symm))

/-- The pair agrees on `whiskerSum` (`4 = 4`). -/
theorem cellLRRL_whiskerSum_eq_cellRLLR : cellLRRL.whiskerSum = cellRLLR.whiskerSum := rfl

/-- The pair agrees on `rSum` (`2 = 2`). -/
theorem cellLRRL_rSum_eq_cellRLLR : cellLRRL.rSum = cellRLLR.rSum := rfl

/-- The pair agrees on `crossSum` (`2 = 2`) — so ALL THREE r1 moments coincide on this composite pair. -/
theorem cellLRRL_crossSum_eq_cellRLLR : cellLRRL.crossSum = cellRLLR.crossSum := rfl

/-- The LEFT member scores `2` on the fourth invariant `nestedCrossSum` (`L R R L` has two `L R L`
subsequences). -/
theorem cellLRRL_nestedCrossSum : cellLRRL.nestedCrossSum = 2 := rfl

/-- The RIGHT member scores `0` on the fourth invariant `nestedCrossSum` (`R L L R` has no `L R L`
subsequence). -/
theorem cellRLLR_nestedCrossSum : cellRLLR.nestedCrossSum = 0 := rfl

/-- ★ The pair has DISTINCT `nestedCrossSum` (`2 ≠ 0`) — the length-3 order moment `crossSum` is blind to. -/
theorem cellLRRL_nestedCrossSum_differs : cellLRRL.nestedCrossSum ≠ cellRLLR.nestedCrossSum := by
  rw [cellLRRL_nestedCrossSum, cellRLLR_nestedCrossSum]
  exact fun contradiction => Nat.noConfusion contradiction

/-- ★★ **The composite pair is NOT bare `TwoCellConv`.**  `nestedCrossSum` — a genuine bare-conv invariant
(`TwoCellConv.nestedCrossSum_eq`, preserved by every `TwoCellStep` including interchange) — scores them `2`
versus `0`.  So two full-conv single-generator whisker chains agreeing on all THREE r1 moments are STILL not
bare-convertible, witnessed by the fourth (length-3 order) invariant. -/
theorem cellLRRL_not_twoCellConv_cellRLLR :
    ¬ TwoCellConv adjunctionModeSignature cellLRRL cellRLLR :=
  fun conv => cellLRRL_nestedCrossSum_differs conv.nestedCrossSum_eq

/-! ## The three-moment candidate is INCOMPLETE over composites -/

/-- ★★ **The three-moment `bareConvCandidate` is INCOMPLETE (over-accepts over COMPOSITES).**  The
`cellLRRL` / `cellRLLR` pair is `bareConvCandidate` (faithful `TwoCellConvFull` PLUS equal `whiskerSum` /
`rSum` / `crossSum`) yet is NOT bare `TwoCellConv`.  This is the FULL-family separating pair r1 left open — a
genuine COMPOSITE (not a single whisker-functoriality law), refuting completeness of the three-moment family. -/
theorem bareConvCandidate_not_complete_composite :
    bareConvCandidate cellLRRL cellRLLR
      ∧ ¬ TwoCellConv adjunctionModeSignature cellLRRL cellRLLR :=
  ⟨⟨cellLRRL_convFull_cellRLLR, cellLRRL_whiskerSum_eq_cellRLLR, cellLRRL_rSum_eq_cellRLLR,
      cellLRRL_crossSum_eq_cellRLLR⟩,
    cellLRRL_not_twoCellConv_cellRLLR⟩

/-! ## The four-moment candidate refinement -/

/-- ★ The **four-moment candidate**: faithful `TwoCellConvFull` PLUS equal `whiskerSum`, `rSum`, `crossSum`, AND
`nestedCrossSum`.  Strictly refines `bareConvCandidate` past the `cellLRRL` / `cellRLLR` blind spot — a sound,
decidable OVER-approximation of bare `TwoCellConv` (still an over-approximation: the structural §2 tower argument
indicates it too is incomplete over longer composites, un-mechanised here). -/
def bareConvCandidate4 {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) : Prop :=
  TwoCellConvFull signature cellFirst cellSecond
    ∧ cellFirst.whiskerSum = cellSecond.whiskerSum
    ∧ cellFirst.rSum = cellSecond.rSum
    ∧ cellFirst.crossSum = cellSecond.crossSum
    ∧ cellFirst.nestedCrossSum = cellSecond.nestedCrossSum

/-- ★ **Soundness (four-moment): bare ⟹ candidate4.**  `ofConv` gives the faithful conjunct; the four moment
invariances give the moment conjuncts. -/
theorem bareConvCandidate4_of_twoCellConv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellFirst cellSecond) :
    bareConvCandidate4 cellFirst cellSecond :=
  ⟨TwoCellConvFull.ofConv conv, conv.whiskerSum_eq, conv.rSum_eq, conv.crossSum_eq, conv.nestedCrossSum_eq⟩

/-- ★ **The four-moment candidate is DECIDABLE at the seed.**  `TwoCellConvFull` is decided ungated; the four
moment equalities are `Nat.decEq`.  Nested `match` — propext-free. -/
def adjunctionDecideBareConvCandidate4
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (bareConvCandidate4 cellFirst cellSecond) :=
  match adjunctionDecideTwoCellConvFull cellFirst cellSecond with
  | isFalse notFull => isFalse (fun candidate => notFull candidate.1)
  | isTrue convFull =>
      match Nat.decEq cellFirst.whiskerSum cellSecond.whiskerSum with
      | isFalse whiskerDiffers => isFalse (fun candidate => whiskerDiffers candidate.2.1)
      | isTrue whiskerAgrees =>
          match Nat.decEq cellFirst.rSum cellSecond.rSum with
          | isFalse rDiffers => isFalse (fun candidate => rDiffers candidate.2.2.1)
          | isTrue rAgrees =>
              match Nat.decEq cellFirst.crossSum cellSecond.crossSum with
              | isFalse crossDiffers => isFalse (fun candidate => crossDiffers candidate.2.2.2.1)
              | isTrue crossAgrees =>
                  match Nat.decEq cellFirst.nestedCrossSum cellSecond.nestedCrossSum with
                  | isFalse nestedDiffers => isFalse (fun candidate => nestedDiffers candidate.2.2.2.2)
                  | isTrue nestedAgrees =>
                      isTrue ⟨convFull, whiskerAgrees, rAgrees, crossAgrees, nestedAgrees⟩

/-- ★ **The four-moment candidate correctly REJECTS the `cellLRRL` / `cellRLLR` pair.**  Adding `nestedCrossSum`
STRICTLY refines the candidate past the three-moment blind spot: its conjunct fails (`2 ≠ 0`), so the refined
candidate excludes the non-bare composite pair the three-moment candidate wrongly accepted. -/
theorem bareConvCandidate4_excludes_cellLRRL_cellRLLR :
    ¬ bareConvCandidate4 cellLRRL cellRLLR :=
  fun candidate => cellLRRL_nestedCrossSum_differs candidate.2.2.2.2

/-- ★ **The four-moment candidate ACCEPTS a genuine bare-conv pair.**  The Eckmann–Hilton parallel-units pair IS
bare `TwoCellConv` (`adjunctionParallelUnitsConv`), so by soundness it satisfies `bareConvCandidate4` — the
refinement is not a reject-everything relation. -/
theorem bareConvCandidate4_accepts_parallelUnits :
    bareConvCandidate4 adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  bareConvCandidate4_of_twoCellConv adjunctionParallelUnitsConv

/-- ★★ **`nestedCrossSum` is FULL-conv-VARIANT** (the hallmark of a real separating invariant): the composite
pair is `TwoCellConvFull` yet `nestedCrossSum` scores it `2` versus `0`.  So `nestedCrossSum` is NOT preserved by
`TwoCellConvFull` (a whisker-functoriality law moves it) — exactly like `crossSum` — confirming the fourth
invariant genuinely refines and the moment family does not terminate at three. -/
theorem cellLRRL_convFull_but_nestedCrossSum_differs :
    TwoCellConvFull adjunctionModeSignature cellLRRL cellRLLR
      ∧ cellLRRL.nestedCrossSum ≠ cellRLLR.nestedCrossSum :=
  ⟨cellLRRL_convFull_cellRLLR, cellLRRL_nestedCrossSum_differs⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the bare-conv three-moment family is INCOMPLETE over COMPOSITES (machine-checked, refuted
by a genuine composite separating pair), and the fourth invariant genuinely refines (so the family does not
collapse at three).**

Delivered (each zero-axiom): the five whisker-functoriality DEFECT vectors (`whiskerLeftUnit` /
`whiskerRightUnit` / `whiskerLeftComp` / `whiskerRightComp` / `whiskerExchange`, with `whiskerExchange` the unique
`crossSum`-only mover); three further bare-conv moments `leftCount` / `coCrossSum` / `nestedCrossSum` with full
bare-conv invariance through the interchange critical pair (`TwoCellConv.{leftCount,coCrossSum,nestedCrossSum}_eq`);
the COMPOSITE separating pair `cellLRRL` / `cellRLLR` (whisker words `L R R L` / `R L L R`, cast-free full-conv
via a two-step `whiskerExchange` chain, agreeing on ALL THREE r1 moments `(4, 2, 2)` yet differing on the fourth
`nestedCrossSum` `2 ≠ 0`, hence NOT bare — `cellLRRL_not_twoCellConv_cellRLLR`); the three-moment incompleteness
over composites (`bareConvCandidate_not_complete_composite` — the full-family separating pair r1 left open); and
the four-moment refinement `bareConvCandidate4` (sound, decidable, excluding the pair, non-vacuous), whose fourth
invariant is itself full-conv-VARIANT (`cellLRRL_convFull_but_nestedCrossSum_differs`) so the tower does not
terminate.

Characterisation (the honest, strengthened wall — the STRUCTURAL reason for the incompleteness, argued in §2,
not separately mechanised beyond the shipped rung): every additive whisker-pattern moment `Σ_gen φ(pattern(gen))`
is a bare-conv invariant (interchange preserves each generator's unlabelled `{L,R}` pattern exactly), so the
COMPLETE bare-invariant is the per-generator pattern MULTISET; `(whiskerSum, rSum, crossSum)` and any FINITE tuple
of bounded-subsequence-length moments (`#L`, `#R`, `#(L-before-R)`, `#(L-before-R-before-L)`, …) is a lossy
shadow — the moment characterisation of bare `TwoCellConv` is an ascending tower.  What is MECHANISED here is the
first rung (three-moment incompleteness, `bareConvCandidate_not_complete_composite`) and that the fourth
invariant genuinely refines (`cellLRRL_convFull_but_nestedCrossSum_differs`); the unboundedness itself is the
structural §2 argument, not a separate Lean proof.  This is NOT absolute undecidability: single-generator
bare-conv is syntactically decidable, and the OPEN converse (full-conv + equal pattern-multiset ⟹ bare) is the
interchange critical-pair coherence (Gratzer), which stays untouched.  Hence `fxMode_hasModeRelativeConvDecision`
is NOT flipped and NOT touched (its terminal disposition in `ModeRelativeMetatheory` is unchanged, not weakened),
the disposed trace / nfCell carriers are NOT re-flipped, and the saturated / faithful decisions are untouched.
This flag records ONLY the machine-checked incompleteness-over-composites + genuine-fourth-invariant upgrade.
`= true`. -/
def fxMode_hasBareConvMomentFamilyProvablyLossy : Bool := true

end FX1Poly.Polygraph
