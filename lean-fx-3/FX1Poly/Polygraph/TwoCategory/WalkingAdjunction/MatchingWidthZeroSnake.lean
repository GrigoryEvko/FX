import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroChordShift

/-! # MatchingWidthZeroSnake — the width-0 snake exclusion + cup-end split (Track B b#5 core)

The location induction's two snake positions (an adjacent pair of forward chords) are ruled out by the
partner INVOLUTION.  The arc stack does this with the private `forwardChordsNotAdjacent`; this file ports
it to the plain `matchingOf` carrier, consuming the width-0 involution
(`matchingOfSpineListZero_partner_isInvolution`, b#1) directly — the make-or-break involution's first
consumer.  Also lands the cup-end open-wire split the sort assembly needs.

  * ★ `matchingForwardChordsNotAdjacent` (b#5 core) — two forward chords at adjacent windows would share an
    endpoint, impossible in the involutive matching: the involution sends the shared endpoint back, not
    forward.  Positivity-free port of `forwardChordsNotAdjacent`.

  * ★ `matchingOpenWiresCupEndSplit` — folding a trailing cup onto a pure-cup width-0 spine grows the
    processed open-wire count by exactly two.  Plain-carrier port of `openWiresCupEndSplit`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two-adjacent-forward-chords exclusion (rides the width-0 involution) -/

/-- ★ **Two forward chords cannot be adjacent (width-0, positivity-free).**  A forward chord
`(windowLow, windowLow + 1)` and another at the NEXT window `(windowLow + 1, windowLow + 2)` share the
endpoint `windowLow + 1`, impossible in the involutive matching: the involution sends `windowLow + 1` back
to `windowLow`, not forward to `windowLow + 2`.  Rules out the degenerate snake position in both descent
directions of the location induction.  Rides the width-0 partner involution
(`matchingOfSpineListZero_partner_isInvolution`, b#1) — NO arc census, NO `0 < bottomCount`. -/
theorem matchingForwardChordsNotAdjacent
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (windowLow : Nat)
    (lowInRange : 0 + windowLow < 0 + (matchingOfSpineList 0 spine).topCount)
    (chordLow : natListGetAt (matchingOfSpineList 0 spine).partner (0 + windowLow)
      = 0 + windowLow + 1)
    (chordHigh : natListGetAt (matchingOfSpineList 0 spine).partner (0 + (windowLow + 1))
      = 0 + (windowLow + 1) + 1) : False := by
  have notFixed : natListGetAt (matchingOfSpineList 0 spine).partner (0 + windowLow) ≠ 0 + windowLow := by
    rw [chordLow]; exact Nat.ne_of_gt (Nat.lt_succ_self (0 + windowLow))
  have inv := matchingOfSpineListZero_partner_isInvolution spine pureCup (0 + windowLow) lowInRange notFixed
  rw [chordLow, Nat.add_assoc 0 windowLow 1, chordHigh] at inv
  have twoZero : 0 + windowLow + 2 = 0 + windowLow := inv
  exact absurd twoZero (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))

/-! ## The cup-end open-wire split (plain carrier) -/

private theorem addLeftVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → leftSummand = 0
  | _, 0, sumZero => sumZero
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue : (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- ★ **Folding a trailing cup onto a pure-cup width-0 spine grows the processed open-wire count by exactly
two** (the cup's two fresh legs).  Plain-carrier port of `openWiresCupEndSplit`. -/
theorem matchingOpenWiresCupEndSplit
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range 0, [], 0, 0⟩ (prefixAtoms ++ [lastCup])).openWires.length
      = (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2 := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  rw [processSpine_append prefixAtoms [lastCup] ⟨List.range 0, [], 0, 0⟩]
  show (stepAtom (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup).openWires.length
    = (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2
  rw [stepAtom_ofCupArity (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup lastDom lastCod]
  exact natListInsertAt_length (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires
    lastCup.leftContext.length
    [(processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh,
      (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh + 1]

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 snake exclusion + cup-end split are ported (Track B b#5 core).**
`matchingForwardChordsNotAdjacent` rules out the two adjacent-forward-chord snake positions of the location
induction, riding the width-0 partner involution (`matchingOfSpineListZero_partner_isInvolution`, b#1 — the
make-or-break's first consumer); `matchingOpenWiresCupEndSplit` gives the cup-end open-wire count.  NO arc
census, NO `0 < bottomCount`.

  What this marker does NOT close (the remaining LOCATE bricks — no gate flag is flipped): the full
  location induction `matchingLocateAux` (bubbling the target cup to the tail by its chord window, via the
  fuel-driven unsnoc + this snake exclusion + the chord-shift descents b#3/b#4 + piece (a)) and the
  direct-Catalan sort assembly closing `WidthZeroPureCupDeterminacy` (c).  All ingredients are shipped.
  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingWidthZeroSnake : Bool := true

end FX1Poly.Polygraph
