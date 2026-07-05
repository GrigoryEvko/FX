import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline

/-! # ArcCupWindowParityDichotomy — a cup cannot nest strictly between another cup's legs

The cup-head discharge (#2152) bubbles a realizing cup back through a prefix, and the descent
step needs, at each passed atom, a CLEAN dichotomy: the descending cup's window is either at or
below the passed atom's window, or fully past it — never strictly between.  For the cap descent
(`arcPairSeated_beforeCapStep_ofTipParities`) the dichotomy is clean because BOTH cap windows
carry `tip` parity, so they sit an even distance apart and the seated pair's freshness kills the
splice.  This file ships the cup analog of exactly that clean dichotomy — proved purely from
PARITY, with no seated pair.

The key fact: a cup atom fires at a `base`-parity window (`adjunctionCupAtom_windowPositionMode`),
and adjacent boundary positions carry OPPOSITE parity (the mode formula's successor step,
`adjunctionModeAtDistance _ (d + 1) = adjunctionOppositeMode (adjunctionModeAtDistance _ d)`).  So
if a preceding cup `P` seats its two legs at `[wP, wP + 2)` (with `wP` at `base`), the strictly
interior position `wP + 1` has `tip` parity — and a descending cup, needing `base` parity, CANNOT
land there.  The nesting-between-a-cup's-legs case is parity-FORBIDDEN, not a genuine interchange
obstruction.  (This corrects the earlier working note that read the cup-past-cup nesting as
non-parity-refutable: for two CUPS it is refutable; only cup-past-CAP crosses parity classes.)

  * `adjunctionModeAtDistance_succ_ne_ofBothBase` — no position and its successor are both `base`
    (the successor flips parity);
  * `adjunctionBaseWindowDichotomy` — two `base`-parity positions are never adjacent-by-one, so a
    Nat trichotomy collapses to below-or-past (`w ≤ wP ∨ wP + 2 ≤ w`);
  * `adjunctionCupAtomWindowDichotomy` — the descent-facing corollary: two cup atoms' windows are
    ordered below-or-past, never nested.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- A boundary position and its immediate successor cannot both carry `base` parity: the mode
formula's successor step is the OPPOSITE mode, and no mode is its own opposite. -/
theorem adjunctionModeAtDistance_succ_ne_ofBothBase
    (startMode : AdjunctionMode) (lowDistance : Nat)
    (lowBase : adjunctionModeAtDistance startMode lowDistance = AdjunctionMode.base)
    (succBase : adjunctionModeAtDistance startMode (lowDistance + 1) = AdjunctionMode.base) :
    False := by
  have oppositeBase :
      adjunctionOppositeMode (adjunctionModeAtDistance startMode lowDistance)
        = AdjunctionMode.base := succBase
  rw [lowBase] at oppositeBase
  exact AdjunctionMode.noConfusion (P := False) oppositeBase

/-- ★ **The base-parity window dichotomy.**  Two boundary positions that both carry `base` parity
are never adjacent-by-one, so the natural-number trichotomy around the passed position collapses:
the target position is at or below the passed one, or at least two past it — never strictly
interior.  This is the parity heart of the cup descent step. -/
theorem adjunctionBaseWindowDichotomy
    {overallSource : adjunctionGraph.Mode}
    (targetWindow passedWindow : Nat)
    (targetBase : adjunctionModeAtDistance overallSource targetWindow = AdjunctionMode.base)
    (passedBase : adjunctionModeAtDistance overallSource passedWindow = AdjunctionMode.base) :
    targetWindow ≤ passedWindow ∨ passedWindow + 2 ≤ targetWindow := by
  cases Nat.lt_or_ge targetWindow (passedWindow + 1) with
  | inl belowSucc => exact Or.inl (Nat.le_of_lt_succ belowSucc)
  | inr atLeastSucc =>
      cases Nat.lt_or_ge targetWindow (passedWindow + 2) with
      | inl belowTwo =>
          have windowIsSucc : targetWindow = passedWindow + 1 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) atLeastSucc
          exact (adjunctionModeAtDistance_succ_ne_ofBothBase overallSource passedWindow
            passedBase (windowIsSucc ▸ targetBase)).elim
      | inr atLeastTwo => exact Or.inr atLeastTwo

/-- ★ **The cup descent step's clean dichotomy.**  Two cup atoms (each firing at a `base`-parity
window, `adjunctionCupAtom_windowPositionMode`) have windows ordered below-or-past: the target
cup's window is at or below the passed cup's, or at least two beyond it.  A cup NEVER nests
strictly between another cup's two legs — the parity refutation feeding the cup bubble producer. -/
theorem adjunctionCupAtomWindowDichotomy
    {overallSource overallTarget : adjunctionGraph.Mode}
    (targetAtom passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (targetIsCup : targetAtom.generatorDom.length = 0)
    (passedIsCup : passedAtom.generatorDom.length = 0) :
    targetAtom.leftContext.length ≤ passedAtom.leftContext.length
      ∨ passedAtom.leftContext.length + 2 ≤ targetAtom.leftContext.length :=
  adjunctionBaseWindowDichotomy targetAtom.leftContext.length passedAtom.leftContext.length
    (adjunctionCupAtom_windowPositionMode targetAtom targetIsCup)
    (adjunctionCupAtom_windowPositionMode passedAtom passedIsCup)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-past-cup parity dichotomy is SHIPPED.**  A cup fires at a
`base`-parity window and adjacent positions carry opposite parity, so two cup atoms' windows are
ordered below-or-past (`adjunctionCupAtomWindowDichotomy`): a cup can never nest strictly between
another cup's two legs.  This is the clean cup analog of the cap descent's
`arcPairSeated_beforeCapStep_ofTipParities` dichotomy, and the concrete refutation of the
nesting case for the cup bubble producer (#2152).  What this marker does NOT claim: the full cup
descent (the cup-past-CAP step, which DOES cross parity classes, plus the inert-path minting) nor
the cup-head extraction it feeds.  `= true`. -/
def fxMode_hasArcCupWindowParityDichotomy : Bool := true

end FX1Poly.Polygraph
