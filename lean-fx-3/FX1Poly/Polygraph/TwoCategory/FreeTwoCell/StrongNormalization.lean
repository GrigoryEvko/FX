import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # mode-3 floor — strong normalization of the `TwoCellStep` 3-polygraph

`FreeTwoCellModel` ships the free 2-cell term model (`RawTwoCellExpr`), the oriented 3-cells
(`TwoCellStep` — the strict-2-category laws as rewrites, closed under congruence + the interchange/Godement
law), and records `fxMode_hasConvergentThreeCellSystem := false` (the CONVERGENCE = termination + confluence
of that 3-polygraph, Gratzer's coherence hurdle).

This file discharges the **termination half** zero-axiom: `TwoCellStep` is STRONGLY NORMALIZING — every free
2-cell is `Acc`-essible under the flipped one-step rewrite.  The naive structural `size` FAILS as a measure
(`whiskerLeft/RightVcomp` strictly INCREASE it; `vcompAssoc` and `interchange` leave it FLAT), which is exactly
Guiraud's 3-dimensional-rewriting obstruction.  We sidestep it with a single **polynomial interpretation**: a
`Nat` weight that is LEFT-HEAVY on vertical composition (`w(vcomp a b) = 2·w(a) + w(b) + 1`) and purely
MULTIPLICATIVE on whiskering (`w(whisker c) = 2·w(c)`, no additive constant).  Under this weight EVERY one of
the twelve `TwoCellStep` rules strictly decreases:

  * the four identity drops drop by ≥ 3 (a `2·w(id)+…` summand vanishes);
  * `vcompAssoc` (left-nest ⟶ right-nest) drops by `2·w(α)+1` — the left-heaviness penalizes deep-left nesting;
  * `whiskerLeft/RightVcomp` (distribute whisker over vcomp) drop by exactly `1` — the multiplicative whisker
    weight makes `2·w(vcomp β γ) > w(vcomp (whisker β) (whisker γ))`;
  * `interchange` (Godement, the deep one) drops by exactly `3` — `hcomp` is the DERIVED Godement product
    `vcomp (whiskerRight …) (whiskerLeft …)`, so both sides expand through the doubling whiskerings, and the
    redex carries three extra unit summands;
  * the four congruences drop by the inductive hypothesis under a strictly-monotone context.

Strong normalization then follows by fuel-bounded `Acc` descent on the weight (structural `Nat` induction on a
fuel bound, never `WellFounded.fix` — which would leak `propext`).

This is the structural floor that the walking-adjunction relative-SN theorems
(`AdjunctionSaturatedNormalization`) are conditioned on: `twoCellStep_isStronglyNormalizing` is precisely their
`structuralStronglyNormalizing` hypothesis, so landing it makes those theorems unconditional.

Zero external dependencies beyond `FreeTwoCellModel`.  Raw Lean 4 + Init.  Every theorem `propext`/`Quot.sound`/
`Classical`/`sorry`/`omega`-free (the arithmetic uses only structural `Nat` lemmas + a hand-built associative-
commutative normalizer `natAddSwapMiddle`; `omega`/`simp`-with-AC/`ac_rfl`/`Nat.add_right_cancel` all leak
`propext` and are avoided).
-/

namespace FX1Poly.Polygraph

/-! ## Zero-axiom associative-commutative `Nat` arithmetic for the weight decreases

The interesting decreases (`vcompAssoc`, `whiskerVcomp`, `interchange`) are pure `Nat` identities of the form
`reduct.weight + positiveGap = redex.weight`.  Proving them zero-axiom (no `omega`, no `simp [Nat.add_comm]`)
needs a controlled associative-commutative normalizer.  `natAddSwapMiddle` (transpose the inner two of a
four-fold sum) is the single primitive; everything else composes from it plus `Nat.add_assoc`. -/

/-- The four-fold transposition `(first + second) + (third + fourth) = (first + third) + (second + fourth)` —
the one AC primitive every weight identity is built from.  Proven from `Nat.add_assoc`/`Nat.add_left_comm`
(both `propext`-free), unlike `simp [Nat.add_comm, Nat.add_assoc]` (leaks `propext`) or `ac_rfl` (leaks). -/
private theorem natAddSwapMiddle (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc, Nat.add_left_comm second third fourth, ← Nat.add_assoc]

/-- Split a doubled sum: `(leftAtom + rightAtom) + (leftAtom + rightAtom) = (leftAtom + leftAtom) +
(rightAtom + rightAtom)` — the diagonal instance of `natAddSwapMiddle`. -/
private theorem natDoubleSplit (leftAtom rightAtom : Nat) :
    (leftAtom + rightAtom) + (leftAtom + rightAtom)
      = (leftAtom + leftAtom) + (rightAtom + rightAtom) :=
  natAddSwapMiddle leftAtom rightAtom leftAtom rightAtom

/-- The `whiskerLeft/RightVcomp` decrease (the redex weight `2·w(vcomp β γ)` exceeds the reduct weight by
exactly `1`): `(childBeta+childBeta+childGamma+1) + (childBeta+childBeta+childGamma+1)
= ((childBeta+childBeta)+(childBeta+childBeta)+(childGamma+childGamma)+1) + 1`.  The right side's first part
is the reduct weight `w(vcomp (whisker β) (whisker γ))`. -/
private theorem natWhiskerDistribDecrease (childBeta childGamma : Nat) :
    (childBeta + childBeta + childGamma + 1) + (childBeta + childBeta + childGamma + 1)
      = ((childBeta + childBeta) + (childBeta + childBeta) + (childGamma + childGamma) + 1) + 1 := by
  rw [natAddSwapMiddle ((childBeta + childBeta) + childGamma) 1 ((childBeta + childBeta) + childGamma) 1,
      natAddSwapMiddle (childBeta + childBeta) childGamma (childBeta + childBeta) childGamma,
      Nat.add_assoc ((childBeta + childBeta) + (childBeta + childBeta)) (childGamma + childGamma) (1 + 1)]

/-- The `vcompAssoc` decrease (left-nested vcomp weight exceeds right-nested by `2·w(α)+1`):
`(childAlpha+childAlpha+childBeta+1) + (childAlpha+childAlpha+childBeta+1) + childGamma + 1
= (childAlpha+childAlpha+(childBeta+childBeta+childGamma+1)+1) + ((childAlpha+childAlpha)+1)`.  The right side's
first summand is the reduct weight `w(vcomp α (vcomp β γ))`. -/
private theorem natVcompAssocDecrease (childAlpha childBeta childGamma : Nat) :
    (childAlpha + childAlpha + childBeta + 1) + (childAlpha + childAlpha + childBeta + 1) + childGamma + 1
      = (childAlpha + childAlpha + (childBeta + childBeta + childGamma + 1) + 1)
          + ((childAlpha + childAlpha) + 1) := by
  rw [natAddSwapMiddle (childAlpha + childAlpha + childBeta) 1 (childAlpha + childAlpha + childBeta) 1,
      natDoubleSplit (childAlpha + childAlpha) childBeta,
      Nat.add_right_comm ((childAlpha + childAlpha) + (childAlpha + childAlpha) + (childBeta + childBeta))
        (1 + 1) childGamma,
      ← Nat.add_assoc
        (((childAlpha + childAlpha) + (childAlpha + childAlpha) + (childBeta + childBeta)) + childGamma) 1 1,
      ← Nat.add_assoc ((childAlpha + childAlpha) + (childBeta + childBeta + childGamma + 1) + 1)
        (childAlpha + childAlpha) 1,
      Nat.add_right_comm ((childAlpha + childAlpha) + (childBeta + childBeta + childGamma + 1)) 1
        (childAlpha + childAlpha),
      Nat.add_right_comm (childAlpha + childAlpha) (childBeta + childBeta + childGamma + 1)
        (childAlpha + childAlpha),
      ← Nat.add_assoc ((childAlpha + childAlpha) + (childAlpha + childAlpha)) (childBeta + childBeta + childGamma)
        1,
      ← Nat.add_assoc ((childAlpha + childAlpha) + (childAlpha + childAlpha)) (childBeta + childBeta) childGamma]

/-- Collect the seven scattered unit summands of a vcomp-shaped interchange reduct to the tail:
`(((varsLeft+(1+1))+(varsRight+1))+1)+(1+1+1) = (varsLeft+varsRight)+(1+1+1+1+1+1+1)`. -/
private theorem natOnesCollectVcomp (varsLeft varsRight : Nat) :
    (((varsLeft + (1 + 1)) + (varsRight + 1)) + 1) + (1 + 1 + 1)
      = (varsLeft + varsRight) + (1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  rw [natAddSwapMiddle varsLeft (1 + 1) varsRight 1, Nat.add_assoc (varsLeft + varsRight) (1 + 1 + 1) 1,
      Nat.add_assoc (varsLeft + varsRight) (1 + 1 + 1 + 1) (1 + 1 + 1)]

/-- Collect the seven scattered unit summands of the interchange redex (the Godement-product side) to the tail:
`(((varsLeft+(1+1))+(1+1)) + ((varsRight+1)+1)) + 1 = (varsLeft+varsRight)+(1+1+1+1+1+1+1)`. -/
private theorem natOnesCollectInterchange (varsLeft varsRight : Nat) :
    (((varsLeft + (1 + 1)) + (1 + 1)) + ((varsRight + 1) + 1)) + 1
      = (varsLeft + varsRight) + (1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  rw [Nat.add_assoc varsLeft (1 + 1) (1 + 1), Nat.add_assoc varsRight 1 1,
      natAddSwapMiddle varsLeft ((1 + 1) + (1 + 1)) varsRight (1 + 1),
      Nat.add_assoc (varsLeft + varsRight) (((1 + 1) + (1 + 1)) + (1 + 1)) 1]

/-- The `interchange`/Godement decrease (redex weight exceeds reduct weight by exactly `3`).  `hcomp` is the
DERIVED product `vcomp (whiskerRight …) (whiskerLeft …)`, so each `doubleX` here is the already-doubled child
weight `w(x)+w(x)` coming through a whiskering; both sides expand through the doubling and share the variable
multiset `{8·α, 4·αUpper, 4·β, 2·βUpper}`, differing only in the unit count (the redex's whiskered Godement
factors carry three extra units).  The variable transposition is one `natAddSwapMiddle`; the units collect on
each side via the two `natOnesCollect…` helpers. -/
private theorem natInterchangeDecrease
    (doubleAlpha doubleAlphaUpper doubleBeta doubleBetaUpper : Nat) :
    (((doubleAlpha + doubleAlpha) + doubleBeta + 1) + ((doubleAlpha + doubleAlpha) + doubleBeta + 1)
        + ((doubleAlphaUpper + doubleAlphaUpper) + doubleBetaUpper + 1) + 1) + (1 + 1 + 1)
      = ((doubleAlpha + doubleAlpha) + doubleAlphaUpper + 1 + 1)
          + ((doubleAlpha + doubleAlpha) + doubleAlphaUpper + 1 + 1)
          + ((doubleBeta + doubleBeta) + doubleBetaUpper + 1 + 1) + 1 := by
  rw [natAddSwapMiddle ((doubleAlpha + doubleAlpha) + doubleBeta) 1
        ((doubleAlpha + doubleAlpha) + doubleBeta) 1,
      natDoubleSplit (doubleAlpha + doubleAlpha) doubleBeta,
      natAddSwapMiddle (((doubleAlpha + doubleAlpha) + doubleAlphaUpper) + 1) 1
        (((doubleAlpha + doubleAlpha) + doubleAlphaUpper) + 1) 1,
      natAddSwapMiddle ((doubleAlpha + doubleAlpha) + doubleAlphaUpper) 1
        ((doubleAlpha + doubleAlpha) + doubleAlphaUpper) 1,
      natDoubleSplit (doubleAlpha + doubleAlpha) doubleAlphaUpper,
      natOnesCollectVcomp (((doubleAlpha + doubleAlpha) + (doubleAlpha + doubleAlpha)) + (doubleBeta + doubleBeta))
        ((doubleAlphaUpper + doubleAlphaUpper) + doubleBetaUpper),
      natOnesCollectInterchange
        (((doubleAlpha + doubleAlpha) + (doubleAlpha + doubleAlpha)) + (doubleAlphaUpper + doubleAlphaUpper))
        ((doubleBeta + doubleBeta) + doubleBetaUpper),
      natAddSwapMiddle ((doubleAlpha + doubleAlpha) + (doubleAlpha + doubleAlpha)) (doubleBeta + doubleBeta)
        (doubleAlphaUpper + doubleAlphaUpper) doubleBetaUpper]

/-! ## The polynomial weight + the per-rule strict decrease -/

/-- The **polynomial weight** of a free 2-cell — the termination measure for the 3-polygraph.  LEFT-HEAVY on
vertical composition (`w(vcomp a b) = w(a)+w(a)+w(b)+1`) so right-association (`vcompAssoc`) strictly decreases;
purely MULTIPLICATIVE on whiskering (`w(whisker c) = w(c)+w(c)`, no additive unit) so distributing a whisker
over a vcomp (`whisker(vcomp) ⟶ vcomp(whisker, whisker)`) strictly decreases.  Same five-case shape as
`RawTwoCellExpr.size`, constant `Nat` motive — recursor `propext`-free. -/
def RawTwoCellExpr.weight {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 1
  | _, _, _, _, .id _ => 1
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.weight + cellAlpha.weight + cellBeta.weight + 1
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.weight + cellBeta.weight
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.weight + cellBeta.weight

/-- ★ **Every `TwoCellStep` rewrite strictly decreases the polynomial weight.**  The twelve-way case analysis:
four identity drops and the two whisker-of-identity drops are direct `Nat` bounds; `vcompAssoc`,
`whiskerLeft/RightVcomp`, and `interchange` are the three polynomial-interpretation identities (above) exposing
a positive gap; the four congruences propagate the inductive hypothesis through a strictly-monotone context.
This is the load-bearing termination lemma for the whole mode-3 floor. -/
theorem TwoCellStep.weight_lt {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {redex reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature redex reduct) : reduct.weight < redex.weight := by
  induction step with
  | vcompIdLeft cellAlpha =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.lt_succ_of_le (Nat.le_add_left cellAlpha.weight (1 + 1))
  | vcompIdRight cellAlpha =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.lt_succ_of_lt (Nat.lt_succ_of_le (Nat.le_add_left cellAlpha.weight cellAlpha.weight))
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.weight]
      rw [natVcompAssocDecrease cellAlpha.weight cellBeta.weight cellGamma.weight]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  | whiskerLeftId oneCell path =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.lt_succ_self 1
  | whiskerRightId path oneCell =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.lt_succ_self 1
  | whiskerLeftVcomp oneCell cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.weight]
      rw [natWhiskerDistribDecrease cellBeta.weight cellGamma.weight]
      exact Nat.lt_succ_self _
  | whiskerRightVcomp oneCell cellAlpha cellBeta =>
      dsimp only [RawTwoCellExpr.weight]
      rw [natWhiskerDistribDecrease cellAlpha.weight cellBeta.weight]
      exact Nat.lt_succ_self _
  | vcompCongrLeft cellBeta innerStep ih =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add ih ih) cellBeta.weight) 1
  | vcompCongrRight cellAlpha innerStep ih =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.add_lt_add_right (Nat.add_lt_add_left ih (cellAlpha.weight + cellAlpha.weight)) 1
  | whiskerLeftCongr oneCell innerStep ih =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.add_lt_add ih ih
  | whiskerRightCongr oneCell innerStep ih =>
      dsimp only [RawTwoCellExpr.weight]
      exact Nat.add_lt_add ih ih
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.weight, RawTwoCellExpr.hcomp]
      rw [natWhiskerDistribDecrease cellAlpha.weight cellAlphaUpper.weight,
          natWhiskerDistribDecrease cellBeta.weight cellBetaUpper.weight,
          ← natInterchangeDecrease (cellAlpha.weight + cellAlpha.weight)
              (cellAlphaUpper.weight + cellAlphaUpper.weight) (cellBeta.weight + cellBeta.weight)
              (cellBetaUpper.weight + cellBetaUpper.weight)]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

/-! ## Strong normalization by fuel-bounded `Acc` descent on the weight -/

/-- ★ **`TwoCellStep` is strongly normalizing.**  Every free 2-cell is `Acc`-essible under the flipped one-step
rewrite — there is no infinite `TwoCellStep` reduction sequence.  This is the TERMINATION half of the
3-polygraph convergence `fxMode_hasConvergentThreeCellSystem` (the confluence half — joining the interchange
critical pair via Newman's lemma — remains).  Proven by structural `Nat` induction on a fuel bound exceeding
the weight, descending via `TwoCellStep.weight_lt`; never `WellFounded.fix` (which leaks `propext`).

This theorem is exactly the `structuralStronglyNormalizing` hypothesis of
`AdjunctionSaturatedNormalization`'s `adjunction{Left,Right}Saturated_isStronglyNormalizing` (instantiate
`signature := adjunctionModeSignature`), so it makes those relative-SN theorems unconditional. -/
theorem twoCellStep_isStronglyNormalizing {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Acc (fun reduct redex => TwoCellStep signature redex reduct) cell := by
  suffices fueled : ∀ (fuel : Nat) {innerSource innerTarget : signature.graph.Mode}
      {innerSourcePath innerTargetPath : ModalityPath signature.graph innerSource innerTarget}
      (innerCell : RawTwoCellExpr signature innerSourcePath innerTargetPath),
      innerCell.weight < fuel →
      Acc (fun reduct redex => TwoCellStep signature redex reduct) innerCell by
    exact fueled (cell.weight + 1) cell (Nat.lt_succ_self _)
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _ _ innerCell weightBelowZero
      exact absurd weightBelowZero (Nat.not_lt_zero _)
  | succ fuel ihFuel =>
      intro _ _ _ _ innerCell weightBelowSucc
      refine Acc.intro innerCell (fun reduct stepToReduct => ?_)
      exact ihFuel reduct
        (Nat.lt_of_lt_of_le (TwoCellStep.weight_lt stepToReduct) (Nat.le_of_lt_succ weightBelowSucc))

end FX1Poly.Polygraph
