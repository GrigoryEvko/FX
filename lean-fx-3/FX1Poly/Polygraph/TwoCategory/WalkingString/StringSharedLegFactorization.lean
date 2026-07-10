import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback

/-! # WalkingString/StringSharedLegFactorization — the WORD-indexed SHARED-LEG (zig-zag STRAIGHTEN) factorization
(FC-3 r5, B1)

The walking-adjunction STRAIGHTEN factor (`WalkingAdjunction/SpineValleyStraightenFactor`) pins the shared-leg
zig-zag geometry — `sharedLegFactorHandednessA` / `sharedLegFactorHandednessB` (the leg SHAPES) and
`cupCapDeletionReconnects` (the endpoint reconnect the delete-chain-surgery consumes) — by SEED LENGTH-RIGIDITY
(`adjunctionPath_eq_of_length_eq`: at the single-colour adjunction, parallel paths of equal length are equal).
That rigidity is FALSE at the walking adjoint triple: out of `base` there are TWO length-1 modalities `F = left`
and `H = coLeft`, both `base ⟶ tip` and DISTINCT (`string_left_ne_coLeft`).  So the length-rigid engine cannot
re-run the STRAIGHTEN sites there.

This file re-derives the STRAIGHTEN geometry keyed on the shared BOUNDARY WORD instead of length-rigidity.  The
inter-atom coherence hands the shared window equation `(*)` (`atomFrameTarget cup = atomFrameSource cap`), and
every pin falls to `composePath_splitPackEqOfPrefixLengthEq` (length-split determinacy of a factorization of ONE
fixed word) — the same split-pack the r4 disjoint-window factorization used, now at the shared-leg split length.
Two genuinely-new nodes with no length-rigid analog appear, both dissolved by the word:

  * `sharedLegSnakeReconnect` — ★ the GENERIC shared-leg reconnect: for a genuine snake window
    `cupCod = outerLeg · innerLeg`, `capDom = innerLeg · outerLeg` (the palindrome the two adjacent generators of
    ONE adjunction make) with the shared window equation and the width-distance-1 relation, the outer legs
    reconnect (`lcCup · rcCup = lcCap · rcCap`) — proved by ONE split-pack (subsuming both the parallel-path and
    the mode-target rigidity the adjunction needed two lemmas for).
  * `sharedLegModeClash` — ★ the MIXED-colour refutation: when the cup's leading leg lands the split at a mode
    the cap's window cannot start from, the split-pack's mid-MODE component contradicts — the shared WORD records
    the colour that lengths threw away.  This is why a mixed pair (`η` opening `F·G` next to `ε'` closing `H·G`,
    both windows length 2) can NEVER be a shared-leg zig-zag: the width-only classifier is colour-blind, but the
    word is not.
  * `stringSharedLegForcesSameColour` — ★ THE genuinely-new lemma the descent oracle needs
    (`StringMatchingValleyDescent` names it): a shared-leg (width-distance-1) cup·cap in the string is
    SAME-colour, so its outer legs reconnect.  Proved by casing the four cup×cap generator combos: the two
    same-colour snakes reconnect (`sharedLegSnakeReconnect`), the two mixed combos are refuted by the
    mode-clash (`sharedLegModeClash`).  No length-rigidity anywhere.
  * `stringCupCapDeletionReconnects` — ★ the STRAIGHTEN endpoint identification (`cupCapDeletionReconnects`
    word-twin): `atomFrameSource cup = atomFrameTarget cap`, wrapping the same-colour reconnect through the
    cup's empty generator source and the cap's empty generator codomain.
  * `stringNatWindowDistance_eq_one_of_zigZag` / `stringZigZagSharedLeg_widthDichotomy` — the colour-blind
    width-dispatch support (the classifier `zigZagSharedLeg` verdict is width-distance-1, which is one of the two
    handednesses), ported verbatim from the length-rigid file (pure `Nat` / classifier, signature-generic).

Non-vacuity: `stringSharedLegReconnect_genuineSnake` reconnects a concrete lower snake `η · ε` at width distance 1
(the class where the reconnect genuinely HOLDS); `stringSharedLegMixedPairExcluded` refutes the equal-length
DISTINCT-word mixed pair `(η : F·G, ε' : H·G)` at width distance 1 — precisely the class where length-rigidity
would UNSOUNDLY equate `F` with `H`.

Raw Lean 4 + Init; the pins are `composePath_splitPackEqOfPrefixLengthEq` on the shared word, the dispatch is
truncated-subtraction `Nat` (hand-rolled cancellation — core `Nat.add_*_cancel` leak propext).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Clean `Nat` bookkeeping (core `Nat.add_*_cancel` / `Nat.sub_*` leak propext) -/

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free). -/
private theorem natAddSubCancelLeftSharedLeg : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftSharedLeg base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightSharedLeg : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightSharedLeg base tail

/-! ## The colour-blind width dispatch (ported verbatim from the length-rigid file) -/

/-- The classifier's `zigZagSharedLeg` verdict at the STRING signature is exactly `natWindowDistance = 1`.
Signature-generic (the classifier reads only widths); a direct clone of the length-rigid
`natWindowDistance_eq_one_of_zigZag`. -/
theorem stringNatWindowDistance_eq_one_of_zigZag
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.zigZagSharedLeg) :
    natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length = 1 := by
  cases isDistance :
      natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length with
  | zero =>
      rw [classifyAdjacentAtoms, classifyAdjacentCupCap, isDistance] at verdict
      exact AdjacentCupCapKind.noConfusion verdict
  | succ predDistance =>
      cases predDistance with
      | zero => rfl
      | succ _ =>
          rw [classifyAdjacentAtoms, classifyAdjacentCupCap, isDistance] at verdict
          exact AdjacentCupCapKind.noConfusion verdict

/-- ★ **The width dichotomy at the STRING signature.**  A `zigZagSharedLeg` pair's two left-context widths differ
by exactly one, so the pair is one of the two handednesses: `cupLeft + 1 = capLeft` (LEFT snake) or
`capLeft + 1 = cupLeft` (RIGHT snake).  Pure `Nat`; a direct clone of `zigZagSharedLeg_widthDichotomy`. -/
theorem stringZigZagSharedLeg_widthDichotomy
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.zigZagSharedLeg) :
    cupAtom.leftContext.length + 1 = capAtom.leftContext.length
      ∨ capAtom.leftContext.length + 1 = cupAtom.leftContext.length := by
  have distanceOne := stringNatWindowDistance_eq_one_of_zigZag cupAtom capAtom verdict
  dsimp only [natWindowDistance] at distanceOne
  rcases Nat.le_total cupAtom.leftContext.length capAtom.leftContext.length with cupLe | capLe
  · left
    obtain ⟨gap, gapEq⟩ := Nat.le.dest cupLe
    rw [← gapEq, natSubAddRightSharedLeg, natAddSubCancelLeftSharedLeg, Nat.zero_add] at distanceOne
    rw [← gapEq, distanceOne]
  · right
    obtain ⟨gap, gapEq⟩ := Nat.le.dest capLe
    rw [← gapEq, natSubAddRightSharedLeg, natAddSubCancelLeftSharedLeg, Nat.add_zero] at distanceOne
    rw [← gapEq, distanceOne]

/-! ## The two generic word-level nodes: the snake reconnect and the mode clash -/

/-- ★ **The GENERIC shared-leg snake reconnect.**  For a genuine snake window — the cup produces
`outerLeg · innerLeg` and the cap consumes the palindrome `innerLeg · outerLeg` (exactly the shapes the two
adjacent generators of ONE adjunction make) — with the shared window equation `(*)` and the width-distance-1
relation `|lcCup| + 1 = |lcCap|`, the OUTER legs reconnect: `lcCup · rcCup = lcCap · rcCap`.  ONE split-pack on
`(*)` at the shared-leg split length pins both `lcCap = lcCup · outerLeg` (site A-left) and
`rcCup = outerLeg · rcCap` (site A-right) — subsuming, in a single call, the parallel-path AND the mode-target
rigidity the length-rigid `sharedLegFactorHandednessA` needed two `adjunctionPath_eq_of_length_eq` invocations
for.  Signature-GENERIC, so it runs at the walking adjoint triple. -/
theorem sharedLegSnakeReconnect {graph : ModeGraph}
    {overallSource overallTarget outerSource innerSource : graph.Mode}
    (outerLeg : graph.Modality outerSource innerSource)
    (innerLeg : graph.Modality innerSource outerSource)
    (lcCup : ModalityPath graph overallSource outerSource)
    (rcCup : ModalityPath graph outerSource overallTarget)
    (lcCap : ModalityPath graph overallSource innerSource)
    (rcCap : ModalityPath graph innerSource overallTarget)
    (coherence :
      composePath lcCup
          (composePath
            (ModalityPath.cons outerLeg (ModalityPath.cons innerLeg (ModalityPath.nil outerSource))) rcCup)
        = composePath lcCap
          (composePath
            (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg (ModalityPath.nil innerSource))) rcCap))
    (widthRel : lcCup.length + 1 = lcCap.length) :
    composePath lcCup rcCup = composePath lcCap rcCap := by
  have wordEq :
      composePath (composePath lcCup (singletonModalityPath outerLeg))
          (ModalityPath.cons innerLeg rcCup)
        = composePath lcCap
          (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg rcCap)) := by
    rw [composePath_assoc lcCup (singletonModalityPath outerLeg) (ModalityPath.cons innerLeg rcCup)]
    exact coherence
  have lengthEq :
      (composePath lcCup (singletonModalityPath outerLeg)).length = lcCap.length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length]
    exact widthRel
  have splitPack := composePath_splitPackEqOfPrefixLengthEq
    (composePath lcCup (singletonModalityPath outerLeg))
    (ModalityPath.cons innerLeg rcCup) lcCap
    (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg rcCap)) wordEq lengthEq
  injection splitPack with _midEqual innerPack
  injection innerPack with prefixEqual suffixEqual
  injection suffixEqual with _srcModeEqual _midModeEqual _tgtModeEqual _modalityEqual tailEqual
  rw [tailEqual, ← prefixEqual]
  exact (composePath_assoc lcCup (singletonModalityPath outerLeg) rcCap).symm

/-- ★ **The MIXED-colour mode clash.**  Two factorizations of the SAME word with equal-length prefixes must land
their split on the SAME mid mode (the split-pack `.fst`); if the two candidate mid modes differ, the word
equation is impossible.  This is the word recording the colour that lengths discard: a cup leg landing the split
at a mode the cap's window cannot start from refutes the shared-leg hypothesis outright.  Signature-generic. -/
theorem sharedLegModeClash {graph : ModeGraph}
    {startMode endMode midOne midTwo : graph.Mode}
    (prefixOne : ModalityPath graph startMode midOne)
    (suffixOne : ModalityPath graph midOne endMode)
    (prefixTwo : ModalityPath graph startMode midTwo)
    (suffixTwo : ModalityPath graph midTwo endMode)
    (wordEq : composePath prefixOne suffixOne = composePath prefixTwo suffixTwo)
    (lengthEq : prefixOne.length = prefixTwo.length)
    (modeClash : midOne ≠ midTwo) : False :=
  modeClash
    (congrArg (fun pack => pack.fst)
      (composePath_splitPackEqOfPrefixLengthEq prefixOne suffixOne prefixTwo suffixTwo wordEq lengthEq))

/-! ## ★ The genuinely-new lemma — a shared-leg cup·cap is SAME-colour, so its outer legs reconnect -/

/-- ★★ **The shared-leg cup·cap is SAME-colour — its OUTER legs reconnect the chain.**  From the inter-atom
shared window equation `(*)` (`atomFrameTarget cup = atomFrameSource cap`) and the width-distance-1 relation
`|lcCup| + 1 = |lcCap|`, the cup's frame SOURCE equals the cap's frame TARGET: `atomFrameSource cup =
atomFrameTarget cap` — the endpoint identification the STRAIGHTEN delete-chain-surgery consumes.  Proved by casing
the four cup×cap generator combos: the two SAME-colour snakes (`η · ε` = `F·G`/`G·F`, `η' · ε'` = `G·H`/`H·G`)
reconnect through `sharedLegSnakeReconnect` (which strips both width-2 windows via ONE split-pack); the two MIXED
combos (`η` with `ε'`, `η'` with `ε`) are refuted by `sharedLegModeClash` — the cup's leading leg lands the shared
split at a mode the cap's window cannot start from (`F` targets `tip`, `H·G` starts at `base`), so the shared word
forbids them.  ★ This is the node the length-rigid engine cannot supply: the width-only classifier is
colour-BLIND, but the shared WORD records the colour, and `string_left_ne_coLeft` (`F ≠ H`) IS exactly the mode
clash the split-pack detects.  The lemma `StringMatchingValleyDescent` names as the STRAIGHTEN-arm prerequisite. -/
theorem stringSharedLegForcesSameColour {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coherence : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (widthRel : cupAtom.leftContext.length + 1 = capAtom.leftContext.length) :
    atomFrameSource cupAtom = atomFrameTarget capAtom := by
  obtain ⟨cupLeftMid, cupRightMid, lcCup, cupDom, cupCod, genCup, rcCup⟩ := cupAtom
  obtain ⟨capLeftMid, capRightMid, lcCap, capDom, capCod, genCap, rcCap⟩ := capAtom
  dsimp only [atomFrameTarget, atomFrameSource, stringFG, stringGF, stringGH, stringHG] at coherence
  cases genCup with
  | counitLower => nomatch isCup
  | counitUpper => nomatch isCup
  | unitLower =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitLower =>
          show composePath lcCup rcCup = composePath lcCap rcCap
          dsimp only [stringFG, stringGF] at coherence
          exact sharedLegSnakeReconnect AdjointTripleModality.left AdjointTripleModality.right
            lcCup rcCup lcCap rcCap coherence widthRel
      | counitUpper =>
          refine (sharedLegModeClash (composePath lcCup (singletonModalityPath AdjointTripleModality.left))
            (ModalityPath.cons AdjointTripleModality.right rcCup) lcCap
            (composePath stringHG rcCap) ?_ ?_ (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCup (singletonModalityPath AdjointTripleModality.left)
                (ModalityPath.cons AdjointTripleModality.right rcCup)]
            exact coherence
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel
  | unitUpper =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitUpper =>
          show composePath lcCup rcCup = composePath lcCap rcCap
          dsimp only [stringGH, stringHG] at coherence
          exact sharedLegSnakeReconnect AdjointTripleModality.right AdjointTripleModality.coLeft
            lcCup rcCup lcCap rcCap coherence widthRel
      | counitLower =>
          refine (sharedLegModeClash (composePath lcCup (singletonModalityPath AdjointTripleModality.right))
            (ModalityPath.cons AdjointTripleModality.coLeft rcCup) lcCap
            (composePath stringGF rcCap) ?_ ?_ (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCup (singletonModalityPath AdjointTripleModality.right)
                (ModalityPath.cons AdjointTripleModality.coLeft rcCup)]
            exact coherence
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel

/-- ★ **The STRAIGHTEN endpoint identification (`cupCapDeletionReconnects` word-twin).**  A width-distance-1
cup·cap pair with matching inter-atom boundary reconnects the chain: `atomFrameSource cup = atomFrameTarget cap`,
so deleting the collapsing snake splices the atoms before the cup onto the atoms after the cap at a common
1-cell.  This is the STRAIGHTEN site the delete-chain-surgery consumes; it is `stringSharedLegForcesSameColour`
under the site's name.  Unlike the adjunction's length-rigid original it carries the width-distance-1 relation as
an explicit hypothesis — the string reconnect holds only for a genuine snake, and the WORD (not the length)
certifies it. -/
theorem stringCupCapDeletionReconnects {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coherence : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (widthRel : cupAtom.leftContext.length + 1 = capAtom.leftContext.length) :
    atomFrameSource cupAtom = atomFrameTarget capAtom :=
  stringSharedLegForcesSameColour cupAtom capAtom isCup isCap coherence widthRel

/-! ## Non-vacuity — the genuine snake reconnects, the mixed pair is excluded -/

/-- ★ **The engine reconnects a genuine lower snake at width distance 1.**  The lower cup `η : id_base ⇒ F·G`
placed at `lcCup = id_base` directly followed by the lower counit `ε : G·F ⇒ id_tip` placed at `lcCap = F`
(width distance 1: `0 + 1 = 1`), sharing the boundary word `F·G·F`.  The outer legs reconnect
(`atomFrameSource cup = atomFrameTarget cap = F`) through `stringCupCapDeletionReconnects` — the class where the
STRAIGHTEN deletion genuinely fires. -/
theorem stringSharedLegReconnect_genuineSnake :
    atomFrameSource
        (⟨AdjointTripleMode.base, AdjointTripleMode.base,
          ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
          ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
          StringTwoCell.unitLower,
          singletonModalityPath AdjointTripleModality.left⟩ :
            SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip)
      = atomFrameTarget
        (⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
          singletonModalityPath AdjointTripleModality.left, stringGF,
          ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
          StringTwoCell.counitLower,
          ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩ :
            SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip) :=
  stringCupCapDeletionReconnects _ _ rfl rfl rfl rfl

/-- ★ **The equal-length DISTINCT-word MIXED pair is EXCLUDED at width distance 1.**  The lower cup
`η : id_base ⇒ F·G` and the upper counit `ε' : H·G ⇒ id_base` (both windows length 2, `F·G ≠ H·G`) CANNOT be a
shared-leg zig-zag: any shared window equation `(*)` between them at width distance 1 is impossible.  The width-
only classifier — colour-blind — could route this MIXED pair to the `zigZagSharedLeg` STRAIGHTEN arm, whose
reconnect would then demand `F = H` (FALSE); the shared WORD refutes the routing at the root.  This is precisely
the class where length-rigidity is UNSOUND, handled correctly by the mode clash. -/
theorem stringSharedLegMixedPairExcluded
    {overallSource overallTarget : AdjointTripleMode}
    (lcCup : ModalityPath adjointTripleGraph overallSource AdjointTripleMode.base)
    (rcCup : ModalityPath adjointTripleGraph AdjointTripleMode.base overallTarget)
    (lcCap : ModalityPath adjointTripleGraph overallSource AdjointTripleMode.base)
    (rcCap : ModalityPath adjointTripleGraph AdjointTripleMode.base overallTarget)
    (coherence : composePath lcCup (composePath stringFG rcCup)
      = composePath lcCap (composePath stringHG rcCap))
    (widthRel : lcCup.length + 1 = lcCap.length) : False := by
  refine sharedLegModeClash (composePath lcCup (singletonModalityPath AdjointTripleModality.left))
    (ModalityPath.cons AdjointTripleModality.right rcCup) lcCap
    (composePath stringHG rcCap) ?_ ?_ (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)
  · rw [composePath_assoc lcCup (singletonModalityPath AdjointTripleModality.left)
        (ModalityPath.cons AdjointTripleModality.right rcCup)]
    exact coherence
  · rw [ModalityPath.length_composePath, singletonModalityPath_length]
    exact widthRel

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the WORD-indexed SHARED-LEG (zig-zag STRAIGHTEN) factorization is machine-checked
(FC-3 r5, B1).**  The five length-rigid STRAIGHTEN sites are re-derived on the shared BOUNDARY WORD:
`sharedLegSnakeReconnect` pins both leg shapes (`lcCap = lcCup · outerLeg`, `rcCup = outerLeg · rcCap`) and the
outer-leg reconnect in ONE `composePath_splitPackEqOfPrefixLengthEq` call (subsuming the parallel-path AND the
mode-target rigidity), and `stringCupCapDeletionReconnects` wraps it into `atomFrameSource cup = atomFrameTarget
cap`.  The genuinely-new node — `stringSharedLegForcesSameColour` (named by `StringMatchingValleyDescent` as the
STRAIGHTEN-arm prerequisite) — proves a shared-leg cup·cap is SAME-colour: the two snakes reconnect, the two
MIXED combos are refuted by `sharedLegModeClash` (the shared WORD records the colour lengths threw away, and
`F ≠ H` IS the mode clash).  Signature-GENERIC, so it runs at the walking adjoint triple where
`adjunctionPath_eq_of_length_eq` is FALSE.  Non-vacuity: `stringSharedLegReconnect_genuineSnake` reconnects a
concrete lower snake `η · ε`; `stringSharedLegMixedPairExcluded` refutes the equal-length DISTINCT-word mixed
pair `(η : F·G, ε' : H·G)` at width distance 1 — the exact class length-rigidity could not touch.

  What this marker does NOT close (gates stay `false`): this is the STRAIGHTEN arm's LOCAL factorization only —
  it does not assemble the merged-`atomFrame` → iterated-leg cast bridge, the delete-chain-surgery `next`, or the
  oracle dispatch; the COMMUTE arm (`StringDisjointWord*`) and Piece II (`StringCellValleyTraceEquiv`) remain.
  `fxString_hasAdjointTripleCompleteness` stays `false`.  `= true`. -/
def fxString_hasSharedLegFactor : Bool := true

end FX1Poly.Polygraph
