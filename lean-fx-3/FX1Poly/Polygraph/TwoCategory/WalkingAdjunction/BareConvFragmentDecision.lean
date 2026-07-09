import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvCompleteness

/-! # mode-3 floor — the bare-`TwoCellConv` FRAGMENT DECISION: bare-conv is DECIDABLE on the single-generator
nil-whisker fragment (it is exactly WORD equality), and the moment tower is INFINITE via that fragment

`BareConvGoldilocks` (r1) and `BareConvCompleteness` (r2) walled the bare `TwoCellConv` decision from the moment
side: each FINITE family of bounded-subsequence `Nat` moments (`whiskerSum`, `rSum`, `crossSum`, `nestedCrossSum`,
…) is a LOSSY shadow of the per-generator whisker-pattern, refuted by an ever-longer composite separating pair.
The recon+lit settlement: the bare structure is the DUAL of a sesquicategory (interchange KEPT, whisker
functoriality DROPPED); after deterministic bookkeeping normalisation, interchange acts as a Mazurkiewicz static
independence relation, so bare-conv is a TRACE word problem — DECIDABLE (Delpeuch–Vicary exchange-move strong
normalisation; Makkai/Forest free strict ω-category word problem).  The finite `Nat` moments are the Parikh image
(order-forgetting), which trace theory proves LOSSY; the COMPLETE bare invariant is the whole per-generator
whisker-pattern (a dependence datum), NOT any finite tuple.

This file lands the DECISIVE positive result of that settlement on the cleanest fragment: the **single-generator
nil-whisker frames** `frameWord w` (the adjunction unit wrapped in a `{L, R}` word `w` of identity-1-cell
whiskers).  There, the complete bare invariant is the WHOLE word `w`, captured by ONE unbounded additive moment
`wordCode` (a bijective base-2 code of the whisker pattern), and bare `TwoCellConv` is EXACTLY word equality —
DECIDABLE.  Since every frame is `TwoCellConvFull`-equal to the bare unit (nil whiskers strip by whisker
functoriality), this is ONE full-conv class shattered into ℕ-many bare classes indexed by the word: the moment
tower made honestly INFINITE, mechanised as an ℕ-indexed family of full-conv-but-not-bare pairs.

## What this file ships (each piece zero-axiom)

  ★ **`RawTwoCellExpr.wordCode`** — the injective additive whisker-pattern code `Σ_gen code(pattern gen)` with
    `code([]) = 0`, `code(L :: p) = 2 code(p) + 1`, `code(R :: p) = 2 code(p) + 2` (bijective base-2, digits
    {1,2}).  Full five-case match, constant `Nat` motive — propext-free.
  ★ **`TwoCellStep.wordCode_eq` / `TwoCellConv.wordCode_eq`** — `wordCode` is a GENUINE bare-conv invariant,
    preserved by every `TwoCellStep` INCLUDING interchange (the Godement critical pair, an eight-atom `Nat`
    reassociation after distributing the `2 *`).  This is the SINGLE UNBOUNDED moment that decides the fragment,
    of which every shipped finite moment (`whiskerSum`, `rSum`, `crossSum`, `nestedCrossSum`) is a lossy shadow.
  ★ **`frameWord`** — the single-generator nil-whisker frame builder `List Bool → RawTwoCellExpr … nil LTR`
    (`false = L = whiskerLeft`, `true = R = whiskerRight`), with `frameWord_wordCode : (frameWord w).wordCode =
    phi w` for the injective word code `phi`, and `phi_injective` (a bijective-base-2 decode via parity /
    halving, all structural, propext/omega-free).
  ★ **`frameWord_twoCellConv_iff`** — bare `TwoCellConv (frameWord w) (frameWord w') ↔ w = w'`: the DECISION,
    plus **`decideFrameBareConv`** giving a total `Decidable (bare TwoCellConv)` on the fragment.  Non-vacuous
    (`#eval`-computes; reproduces r1's whiskerExchange and r2's `cellLRRL` / `cellRLLR` as frames `[false,true]`
    / `[true,false]` and `[false,true,true,false]` / `[true,false,false,true]`).
  ★ **`frameWord_bubble` / `frameWord_tower_separates`** — the INFINITE tower: for every `n`,
    `frameWord (L^{n+1} R)` and `frameWord (R L^{n+1})` are `TwoCellConvFull` (a cast-free `nilWhiskerExchange`
    bubble-sort chain) yet NOT bare `TwoCellConv` (distinct `wordCode`).  One full-conv class, ℕ-many bare
    classes — the moment tower is infinite, witnessed on the fragment.

## What stays DEFERRED — `fxMode_hasModeRelativeConvDecision` NOT flipped

The GENERAL (multi-generator) bare `TwoCellConv` decision is the interchange critical-pair coherence (Gratzer);
the trace/dependence-graph route settles it decidable in principle, but its mechanised total decider needs the
full pattern-dependence invariant (Arm A's `patternMultiset` completeness) — not landed here.  This file lands
the FRAGMENT decision (positive) and the infinite-tower wall (fragment-witnessed).
`fxMode_hasBareConvDecidedOnSingleGeneratorFragment` and `fxMode_hasBareConvMomentTowerInfiniteViaFragment`
record exactly those; `fxMode_hasModeRelativeConvDecision` (its terminal disposition in `ModeRelativeMetatheory`)
is NOT flipped, NOT touched, NOT weakened; r1 / r2 soundness / statements are NOT weakened; the disposed
trace / nfCell carriers are NOT re-flipped; the saturated / faithful decisions are untouched.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
moments are constant-`Nat`-motive full-enum matches; the `_eq` lemmas are `induction` + explicit `Nat.add_*` /
`Nat.left_distrib` rewrites — never `omega`/`simp`/`ac_rfl`; `phi_injective` is structural parity/halving with
`Nat.noConfusion` / `Bool.noConfusion`; the fragment `DecidableEq (List Bool)` is a hand-rolled structural
`listBoolDecEq`; the bubble chain is cast-free `nilWhiskerExchange`).  Per-declaration `#assert_no_axioms` in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The injective additive whisker-pattern code -/

/-- The **whisker-pattern word code** of a free 2-cell — `Σ` over generators of a bijective base-2 code of the
generator's `{L, R}` whisker word (outermost letter last): `code([]) = 0`, `code(L :: p) = 2 code(p) + 1`,
`code(R :: p) = 2 code(p) + 2`.  As an additive per-generator moment: a generator / identity scores `0`; a
`vcomp` sums the factors; a LEFT whisker maps `code(p) ↦ 2 code(p) + 1` per generator (`2 * body.wordCode +
body.generatorCount`); a RIGHT whisker maps `code(p) ↦ 2 code(p) + 2` per generator (`2 * body.wordCode +
2 * body.generatorCount`).  Digits `{1, 2}` make the code a bijection with words, so on the single-generator
fragment `wordCode` is a COMPLETE (injective) invariant — the unbounded moment the finite ones only shadow.
Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.wordCode {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.wordCode + cellBeta.wordCode
  | _, _, _, _, .whiskerLeft _ cellBeta => 2 * cellBeta.wordCode + cellBeta.generatorCount
  | _, _, _, _, .whiskerRight _ cellBeta => 2 * cellBeta.wordCode + 2 * cellBeta.generatorCount

/-! ## `Nat` reassociation shapes for the interchange rebracketing -/

/-- Middle-four exchange for `Nat` addition.  Propext-free (`Nat.add_assoc` / `Nat.add_left_comm`). -/
private theorem nat_add_middle_four_wc (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm second third fourth]

/-- Eight-term shuffle for `Nat` addition — interchange rebrackets the four sub-cells' `(2·wordCode,
coefficient·generatorCount)` pairs; both Godement orders sum the same eight atoms.  Six fully-instantiated
middle-four exchanges (deterministic `rw` targets), propext-free. -/
private theorem nat_add_shuffle_eight_wc (a b c d e f g h : Nat) :
    ((a + b) + (c + d)) + ((e + f) + (g + h))
      = ((a + c) + (e + g)) + ((b + d) + (f + h)) := by
  rw [nat_add_middle_four_wc (a + b) (c + d) (e + f) (g + h)]
  rw [nat_add_middle_four_wc a b e f]
  rw [nat_add_middle_four_wc c d g h]
  rw [nat_add_middle_four_wc (a + e) (b + f) (c + g) (d + h)]
  rw [nat_add_middle_four_wc a e c g]
  rw [nat_add_middle_four_wc b f d h]

/-! ## `wordCode` is a bare-conv invariant -/

/-- ★ **`wordCode` is invariant under one 3-cell rewrite — INCLUDING interchange.**  Identity removal drops a
`0` factor; re-association / whisker distribution rearrange the sum (`Nat.left_distrib` to expand the `2 * (_ +
_)`, then a middle-four exchange); the INTERCHANGE law rebrackets the eight moment atoms
(`nat_add_shuffle_eight_wc` after three distributions — both Godement orders sum the same eight
`(2·wordCode, coefficient·generatorCount)` atoms).  Left / right whiskering thread the generator-count invariance
of the sub-step (`TwoCellStep.generatorCount_eq`) as well as the inductive hypothesis.  By induction on the
step. -/
theorem TwoCellStep.wordCode_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.wordCode = reduct.wordCode := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.wordCode
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.wordCode cellBeta.wordCode cellGamma.wordCode
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.wordCode, RawTwoCellExpr.generatorCount]
      rw [Nat.left_distrib]
      exact nat_add_middle_four_wc (2 * cellBeta.wordCode) (2 * cellGamma.wordCode)
        cellBeta.generatorCount cellGamma.generatorCount
  | whiskerRightVcomp _ cellAlpha cellBeta =>
      dsimp only [RawTwoCellExpr.wordCode, RawTwoCellExpr.generatorCount]
      rw [Nat.left_distrib, Nat.left_distrib]
      exact nat_add_middle_four_wc (2 * cellAlpha.wordCode) (2 * cellBeta.wordCode)
        (2 * cellAlpha.generatorCount) (2 * cellBeta.generatorCount)
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.wordCode]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.wordCode]; rw [inductionHypothesis]
  | whiskerLeftCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.wordCode]
      rw [inductionHypothesis, subStep.generatorCount_eq]
  | whiskerRightCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.wordCode]
      rw [inductionHypothesis, subStep.generatorCount_eq]
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.wordCode, RawTwoCellExpr.generatorCount]
      rw [Nat.left_distrib, Nat.left_distrib, Nat.left_distrib]
      exact nat_add_shuffle_eight_wc
        (2 * cellAlpha.wordCode) (2 * cellAlphaUpper.wordCode)
        (2 * cellAlpha.generatorCount) (2 * cellAlphaUpper.generatorCount)
        (2 * cellBeta.wordCode) (2 * cellBetaUpper.wordCode)
        cellBeta.generatorCount cellBetaUpper.generatorCount

/-- **`wordCode` is invariant under 2-cell convertibility.**  A single step is `wordCode_eq`; reflexivity is
`rfl`; symmetry / transitivity chain through `Eq`.  A genuine BARE-conv invariant surviving interchange, and the
UNBOUNDED one that decides the single-generator fragment (every finite bounded-subsequence moment is its lossy
shadow). -/
theorem TwoCellConv.wordCode_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.wordCode = reduct.wordCode := by
  induction conv with
  | ofStep step => exact step.wordCode_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## Structural `Nat` parity / halving helpers for the word-code injectivity (propext/omega-free) -/

/-- The low bit of a `Nat` (`true` iff even) — structural on the `n + 2` pattern.  Distinguishes even from odd
without `omega`. -/
def isEvenBit : Nat → Bool
  | 0 => true
  | 1 => false
  | predPred + 2 => isEvenBit predPred

/-- `2 * a` is even.  Structural induction: `2 * (a + 1) ≡ (2 * a) + 2` peels the `+ 2` pattern. -/
theorem isEvenBit_two_mul : (a : Nat) → isEvenBit (2 * a) = true
  | 0 => rfl
  | a + 1 => isEvenBit_two_mul a

/-- `2 * b + 1` is odd.  Structural induction: `2 * (b + 1) + 1 ≡ (2 * b + 1) + 2` peels the `+ 2` pattern. -/
theorem isEvenBit_two_mul_add_one : (b : Nat) → isEvenBit (2 * b + 1) = false
  | 0 => rfl
  | b + 1 => isEvenBit_two_mul_add_one b

/-- Even never equals odd: `2 * a = 2 * b + 1` is impossible.  `isEvenBit` scores the two sides `true` versus
`false`. -/
theorem two_mul_ne_two_mul_add_one {a b : Nat} (h : 2 * a = 2 * b + 1) : False := by
  have hEven : isEvenBit (2 * a) = true := isEvenBit_two_mul a
  rw [h, isEvenBit_two_mul_add_one b] at hEven
  exact Bool.noConfusion hEven

/-- Floor-halving of a `Nat` — structural on the `n + 2` pattern.  A left inverse of `2 * ·`. -/
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | predPred + 2 => halve predPred + 1

/-- `halve` is a left inverse of `2 * ·`.  Structural induction: `halve (2 * (a + 1)) ≡ halve (2 * a) + 1`. -/
theorem halve_two_mul : (a : Nat) → halve (2 * a) = a
  | 0 => rfl
  | a + 1 => congrArg (· + 1) (halve_two_mul a)

/-- Left cancellation of `2 *`: `2 * a = 2 * b → a = b`, via the `halve` left inverse (no `Nat.le`, no
`omega`). -/
theorem two_mul_cancel {a b : Nat} (h : 2 * a = 2 * b) : a = b :=
  (halve_two_mul a).symm.trans ((congrArg halve h).trans (halve_two_mul b))

/-! ## The single-generator nil-whisker frames -/

/-- The base-mode identity 1-cell (the empty modality path) — the whisker 1-cell every frame uses. -/
abbrev frameBaseNil : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- ★ The **single-generator nil-whisker frame** of a `{L, R}` word — the adjunction unit wrapped in identity-1-cell
whiskers, outermost letter first (`false = L = whiskerLeft`, `true = R = whiskerRight`).  Every letter is the
identity 1-cell, so all frames share the boundary `nil ⇒ (left then right)` DEFINITIONALLY (no boundary cast).
The fully-applied `@`-constructor form pins the whisker 1-cell (a bare `whiskerLeft (identityPath …)` under the
declared codomain leaves the 1-cell an unsolved index metavariable). -/
def frameWord : List Bool → RawTwoCellExpr adjunctionModeSignature frameBaseNil adjunctionLeftThenRight
  | [] => adjunctionUnitTwoCell
  | false :: w =>
      @RawTwoCellExpr.whiskerLeft adjunctionModeSignature
        AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
        frameBaseNil frameBaseNil adjunctionLeftThenRight (frameWord w)
  | true :: w =>
      @RawTwoCellExpr.whiskerRight adjunctionModeSignature
        AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
        frameBaseNil adjunctionLeftThenRight frameBaseNil (frameWord w)

/-- Every frame has generator count `1` (it wraps exactly one generator). -/
theorem frameWord_generatorCount : (w : List Bool) → (frameWord w).generatorCount = 1
  | [] => rfl
  | false :: w => by dsimp only [frameWord, RawTwoCellExpr.generatorCount]; exact frameWord_generatorCount w
  | true :: w => by dsimp only [frameWord, RawTwoCellExpr.generatorCount]; exact frameWord_generatorCount w

/-- The injective **word code** of a `{L, R}` word — the bijective base-2 numeral with digits `{1, 2}` matching
`wordCode ∘ frameWord`: `phi [] = 0`, `phi (L :: w) = 2 phi w + 1`, `phi (R :: w) = 2 phi w + 2`. -/
def phi : List Bool → Nat
  | [] => 0
  | false :: w => 2 * phi w + 1
  | true :: w => 2 * phi w + 2

/-- ★ **`wordCode` of a frame is `phi` of its word.**  By induction: the left / right whisker's `2 * … +
{generatorCount, 2 * generatorCount}` recursion is exactly `phi`'s `2 · + {1, 2}`, using `frameWord_generatorCount
= 1`. -/
theorem frameWord_wordCode : (w : List Bool) → (frameWord w).wordCode = phi w
  | [] => rfl
  | false :: w => by
      dsimp only [frameWord, RawTwoCellExpr.wordCode, phi]
      rw [frameWord_generatorCount w, frameWord_wordCode w]
  | true :: w => by
      dsimp only [frameWord, RawTwoCellExpr.wordCode, phi]
      rw [frameWord_generatorCount w, frameWord_wordCode w]

/-- A cons word has non-zero `phi` (`2 · + 1` or `2 · + 2` is a successor). -/
theorem phi_cons_ne_zero (bit : Bool) (w : List Bool) (h : phi (bit :: w) = 0) : False := by
  cases bit with
  | false => dsimp only [phi] at h; exact Nat.noConfusion h
  | true => dsimp only [phi] at h; exact Nat.noConfusion h

/-- ★ **`phi` is injective.**  Structural induction on the first word with case split on the second, using: `phi`
of a cons is a successor (`phi_cons_ne_zero`, `Nat.noConfusion`); heads agree by parity
(`two_mul_ne_two_mul_add_one`); tails by `2 *`-cancellation (`two_mul_cancel`) + the inductive hypothesis.  All
propext/omega-free. -/
theorem phi_injective : (w wOther : List Bool) → phi w = phi wOther → w = wOther := by
  intro w
  induction w with
  | nil =>
      intro wOther h
      cases wOther with
      | nil => rfl
      | cons bit tailOther => exact (phi_cons_ne_zero bit tailOther h.symm).elim
  | cons head tail ih =>
      intro wOther h
      cases wOther with
      | nil => exact (phi_cons_ne_zero head tail h).elim
      | cons bit tailOther =>
          cases head with
          | false =>
              cases bit with
              | false =>
                  dsimp only [phi] at h
                  exact congrArg (fun t => false :: t) (ih tailOther (two_mul_cancel (Nat.succ.inj h)))
              | true =>
                  dsimp only [phi] at h
                  exact (two_mul_ne_two_mul_add_one (Nat.succ.inj h)).elim
          | true =>
              cases bit with
              | false =>
                  dsimp only [phi] at h
                  exact (two_mul_ne_two_mul_add_one (Nat.succ.inj h).symm).elim
              | true =>
                  dsimp only [phi] at h
                  exact congrArg (fun t => true :: t)
                    (ih tailOther (two_mul_cancel (Nat.succ.inj (Nat.succ.inj h))))

/-! ## The fragment decision: bare `TwoCellConv` on frames is exactly word equality -/

/-- Hand-rolled structural `DecidableEq (List Bool)` — cons-only, `List.noConfusion` / `Bool.decEq`, propext-free
(the derived instance is clean too, but this keeps the fragment decider self-contained and audit-transparent). -/
def listBoolDecEq : (w wOther : List Bool) → Decidable (w = wOther)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by injection h)
  | _ :: _, [] => isFalse (fun h => by injection h)
  | bit :: tail, bitOther :: tailOther =>
      match Bool.decEq bit bitOther with
      | isFalse headDiffers => isFalse (fun h => by injection h with hHead _; exact headDiffers hHead)
      | isTrue headAgrees =>
          match listBoolDecEq tail tailOther with
          | isFalse tailDiffers => isFalse (fun h => by injection h with _ hTail; exact tailDiffers hTail)
          | isTrue tailAgrees => isTrue (by cases headAgrees; cases tailAgrees; rfl)

/-- ★★ **The fragment decision (relation form).**  Bare `TwoCellConv` between two single-generator nil-whisker
frames is EXACTLY equality of their whisker words.  `(→)`: `wordCode` is a bare-conv invariant
(`TwoCellConv.wordCode_eq`) and `phi` is injective, so equal frames force equal words.  `(←)`: reflexivity.  So on
the fragment the finite-moment tower collapses into ONE decidable invariant (`wordCode`) — the positive half of
the trace-word-problem settlement. -/
theorem frameWord_twoCellConv_iff (w wOther : List Bool) :
    TwoCellConv adjunctionModeSignature (frameWord w) (frameWord wOther) ↔ w = wOther := by
  constructor
  · intro conv
    exact phi_injective w wOther
      ((frameWord_wordCode w).symm.trans (conv.wordCode_eq.trans (frameWord_wordCode wOther)))
  · intro hEq; subst hEq; exact TwoCellConv.refl _

/-- ★★ **The fragment decision (decision-procedure form).**  A TOTAL `Decidable (bare TwoCellConv)` on the
single-generator nil-whisker fragment: decide word equality (`listBoolDecEq`), then transport across
`frameWord_twoCellConv_iff`.  Nested `match` — propext-free. -/
def decideFrameBareConv (w wOther : List Bool) :
    Decidable (TwoCellConv adjunctionModeSignature (frameWord w) (frameWord wOther)) :=
  match listBoolDecEq w wOther with
  | isTrue hEq => isTrue (by subst hEq; exact TwoCellConv.refl _)
  | isFalse hNe => isFalse (fun conv => hNe ((frameWord_twoCellConv_iff w wOther).mp conv))

/-- The fragment decider as a `Bool` — for `#eval` non-vacuity. -/
def frameBareConvBool (w wOther : List Bool) : Bool :=
  @decide _ (decideFrameBareConv w wOther)

/-! ## Non-vacuity + the fragment subsumes the r1 / r2 fixtures -/

-- The decider computes: `true` on a reflexive (equal-word) pair, `false` on the whiskerExchange `L R` / `R L`.
#eval frameBareConvBool [false] [false]           -- true
#eval frameBareConvBool [false, true] [true, false]  -- false

/-- The decider ACCEPTS a genuine bare-conv (reflexive) pair — its `isTrue` side is inhabited. -/
theorem frameWord_selfConv :
    TwoCellConv adjunctionModeSignature (frameWord [false]) (frameWord [false]) :=
  TwoCellConv.refl _

/-- The whiskerExchange LEFT side (r1) IS the frame `[L, R]` — DEFINITIONALLY. -/
theorem whiskerExchangeLHS_eq_frameWord : whiskerExchangeLHS = frameWord [false, true] := rfl

/-- The whiskerExchange RIGHT side (r1) IS the frame `[R, L]` — DEFINITIONALLY. -/
theorem whiskerExchangeRHS_eq_frameWord : whiskerExchangeRHS = frameWord [true, false] := rfl

/-- The composite separating pair `cellLRRL` (r2) IS the frame `[L, R, R, L]` — DEFINITIONALLY. -/
theorem cellLRRL_eq_frameWord : cellLRRL = frameWord [false, true, true, false] := rfl

/-- The composite separating pair `cellRLLR` (r2) IS the frame `[R, L, L, R]` — DEFINITIONALLY. -/
theorem cellRLLR_eq_frameWord : cellRLLR = frameWord [true, false, false, true] := rfl

/-- ★ The fragment decider REPRODUCES r1's whiskerExchange refutation: `[L, R]` and `[R, L]` are NOT
bare-convertible (distinct words). -/
theorem frameWord_LR_not_twoCellConv_RL :
    ¬ TwoCellConv adjunctionModeSignature (frameWord [false, true]) (frameWord [true, false]) := by
  intro conv
  have hWord := (frameWord_twoCellConv_iff _ _).mp conv
  injection hWord with hHead _
  exact Bool.noConfusion hHead

/-- ★ The fragment decider REPRODUCES r2's composite refutation: `[L, R, R, L]` and `[R, L, L, R]` are NOT
bare-convertible (distinct words). -/
theorem frameWord_LRRL_not_twoCellConv_RLLR :
    ¬ TwoCellConv adjunctionModeSignature
        (frameWord [false, true, true, false]) (frameWord [true, false, false, true]) := by
  intro conv
  have hWord := (frameWord_twoCellConv_iff _ _).mp conv
  injection hWord with hHead _
  exact Bool.noConfusion hHead

/-! ## The infinite tower: one full-conv class, ℕ-many bare classes -/

/-- The `L`-word `L^n` (`n` identity left whiskers). -/
def falseWord : Nat → List Bool
  | 0 => []
  | n + 1 => false :: falseWord n

/-- The tower LEFT member word `L^n R` — `n` left whiskers over one right whisker. -/
def bubbleLeft : Nat → List Bool
  | 0 => [true]
  | n + 1 => false :: bubbleLeft n

/-- The tower RIGHT member word `R L^n` — one right whisker over `n` left whiskers.  Same letter multiset as
`bubbleLeft n` (one `R`, `n` `L`s), so the frames are `TwoCellConvFull`; different word for `n ≥ 1`, so NOT
bare. -/
def bubbleRight (n : Nat) : List Bool := true :: falseWord n

/-- ★ **The bubble chain — every `L^n R` frame is `TwoCellConvFull` to its `R L^n` frame.**  Cast-free induction:
the outer `L` whiskers the inductive full-conv, then the innermost `L ◁ (R ▷ _)` disjoint whiskers commute by the
cast-free `nilWhiskerExchange`, moving the single `R` up past one `L`.  Uses ONLY whisker functoriality
(`whiskerLeftCongr`, `nilWhiskerExchange`) — the laws bare `TwoCellConv` lacks. -/
theorem frameWord_bubble : (n : Nat) →
    TwoCellConvFull adjunctionModeSignature (frameWord (bubbleLeft n)) (frameWord (bubbleRight n))
  | 0 => TwoCellConvFull.refl _
  | n + 1 =>
      TwoCellConvFull.trans
        (@TwoCellConvFull.whiskerLeftCongr adjunctionModeSignature
          AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
          frameBaseNil frameBaseNil adjunctionLeftThenRight
          (frameWord (bubbleLeft n)) (frameWord (bubbleRight n)) (frameWord_bubble n))
        (nilWhiskerExchange (frameWord (falseWord n)))

/-- For `n ≥ 1` the two tower words differ (heads `L` versus `R`). -/
theorem bubbleLeft_ne_bubbleRight (n : Nat) : bubbleLeft (n + 1) = bubbleRight (n + 1) → False := by
  intro h
  dsimp only [bubbleLeft, bubbleRight] at h
  injection h with hHead _
  exact Bool.noConfusion hHead

/-- ★★ **The infinite tower.**  For EVERY `n`, the frames `frameWord (L^{n+1} R)` and `frameWord (R L^{n+1})` are
`TwoCellConvFull` (the cast-free bubble chain) yet NOT bare `TwoCellConv` (distinct `wordCode`, via the fragment
decision).  So a SINGLE `TwoCellConvFull` orbit shatters into ℕ-many bare `TwoCellConv` classes indexed by the
word — the moment tower is INFINITE (no finite bounded-subsequence family can separate all these frames, which
`wordCode` alone does).  This upgrades r2's rung-1 lossiness flag to a fragment-witnessed infinite tower. -/
theorem frameWord_tower_separates (n : Nat) :
    TwoCellConvFull adjunctionModeSignature
        (frameWord (bubbleLeft (n + 1))) (frameWord (bubbleRight (n + 1)))
      ∧ ¬ TwoCellConv adjunctionModeSignature
          (frameWord (bubbleLeft (n + 1))) (frameWord (bubbleRight (n + 1))) :=
  ⟨frameWord_bubble (n + 1),
    fun conv => bubbleLeft_ne_bubbleRight n ((frameWord_twoCellConv_iff _ _).mp conv)⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — bare `TwoCellConv` is DECIDABLE on the single-generator nil-whisker fragment (it is exactly
word equality), and the moment tower is INFINITE, witnessed on that fragment.**

Delivered (each zero-axiom): the injective additive whisker-pattern code `RawTwoCellExpr.wordCode` with full
bare-conv invariance through the interchange critical pair (`TwoCellConv.wordCode_eq`); the frame builder
`frameWord` with `frameWord_wordCode = phi` and the structural, propext/omega-free `phi_injective`; the FRAGMENT
DECISION `frameWord_twoCellConv_iff` (bare-conv ↔ word equality) and its total decider `decideFrameBareConv`
(`#eval`-computing `frameBareConvBool`), reproducing r1's whiskerExchange (`[L,R]` / `[R,L]`) and r2's composite
(`[L,R,R,L]` / `[R,L,L,R]`) as frames it DEFINITIONALLY equals; and the INFINITE tower `frameWord_tower_separates`
— for every `n`, `frameWord (L^{n+1} R)` and `frameWord (R L^{n+1})` are `TwoCellConvFull` (a cast-free
`nilWhiskerExchange` bubble chain) yet NOT bare (distinct `wordCode`), so one full-conv orbit carries ℕ-many bare
classes.

Deferred (the genuine, honest wall): the GENERAL (multi-generator) bare `TwoCellConv` decision.  The recon+lit
settlement is that it is DECIDABLE in principle (the bare structure is the dual of a sesquicategory; after
bookkeeping normalisation interchange is a Mazurkiewicz static independence relation, so bare-conv is a TRACE word
problem — Delpeuch–Vicary / Makkai–Forest), with the COMPLETE invariant the per-generator whisker-pattern
DEPENDENCE datum (NOT the order-forgetting Parikh moments, which trace theory proves lossy — matching r1 / r2 /
this file's tower).  Its mechanised TOTAL decider needs that full pattern-dependence completeness (Arm A's
`patternMultiset`), the interchange critical-pair coherence (Gratzer), which is NOT landed here.  Hence
`fxMode_hasModeRelativeConvDecision` is NOT flipped and NOT touched (its terminal disposition in
`ModeRelativeMetatheory` is unchanged, not weakened); r1 / r2 soundness / statements are NOT weakened; the disposed
trace / nfCell carriers are NOT re-flipped; the saturated / faithful decisions are untouched.  This flag records
ONLY the fragment decision.  `= true`. -/
def fxMode_hasBareConvDecidedOnSingleGeneratorFragment : Bool := true

/-- **★ ESTABLISHED — the bare-conv moment tower is INFINITE, witnessed on the single-generator fragment.**  One
`TwoCellConvFull` orbit (all frames strip to the unit by whisker functoriality) carries ℕ-many distinct bare
`TwoCellConv` classes, separated ONLY by the unbounded `wordCode` (`frameWord_tower_separates`); every FINITE
family of bounded-subsequence `Nat` moments (`whiskerSum`, `rSum`, `crossSum`, `nestedCrossSum`, …) is the Parikh
shadow of the whisker pattern and therefore CANNOT separate all these frames.  This upgrades r2's rung-1
`fxMode_hasBareConvMomentFamilyProvablyLossy` to the full fragment-witnessed tower — NOT undecidability (the
fragment is DECIDED by `wordCode`; the general decision is the deferred Gratzer coherence).  `= true`. -/
def fxMode_hasBareConvMomentTowerInfiniteViaFragment : Bool := true

end FX1Poly.Polygraph

