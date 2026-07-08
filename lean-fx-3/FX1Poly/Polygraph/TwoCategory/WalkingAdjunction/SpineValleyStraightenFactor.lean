import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyClassifier
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducer

/-! # mode-3 keystone — Piece I STRAIGHTEN 2a: the shared-leg factorization is LOCALLY FORCED

The residual `CellStraightenStepInput` (#2185) was framed as a GLOBAL arc-lift: to STRAIGHTEN a `zigZagSharedLeg`
redex you were said to need the arc `matchingOf` to certify partner-hood.  This file refutes that framing at the
combinatorial root, matching the RV/FM literature verdict (`matchingOf` is the NF read-off, NOT an input to the
descent step): the shared-leg factorization is a PURELY LOCAL consequence of two facts the descent already has in
hand at the redex, with NO consultation of `matchingOf` / `partnerIndexOf` / `arcStructureOf`:

  * the inter-atom **boundary coherence** `atomFrameTarget cupAtom = atomFrameSource capAtom` — read off the
    cell's OWN realized chain by `framedChain_pairPathCoherence` (exactly what the COMMUTE producer uses); and
  * the classifier's **`zigZagSharedLeg`** verdict — a pure LENGTH fact, `natWindowDistance = 1`.

From these, seed rigidity (`adjunctionPath_eq_of_length_eq`: parallel walking-adjunction 1-cells of equal length
are equal) FORCES the shared-leg factorization, in one of exactly two handednesses:

  * ★ **`natWindowDistance_eq_one_of_zigZag` / `zigZagSharedLeg_widthDichotomy`** — the verdict means the two
    left-context widths differ by exactly one, so `cupLeft + 1 = capLeft` (handedness A, the LEFT snake) or
    `capLeft + 1 = cupLeft` (handedness B, the RIGHT snake).  Pure `Nat`.
  * ★ **`sharedLegFactorHandednessA`** — width-A: the cap's left context IS the cup's left context extended by the
    shared leg `left`, and the cup's right context IS the shared leg `left` prepended to the cap's right context:
    `lcCap = lcCup · L`, `rcCup = L · rcCap`.  A genuine cup·cap partner in the LEFT-snake orientation.
  * ★ **`sharedLegFactorHandednessB`** — width-B (mirror): `lcCup = lcCap · R`, `rcCap = R · rcCup`.  The
    RIGHT-snake orientation.

Both are proven from the boundary word equality + the width relation by seed rigidity ALONE — no arc read, no
`matchingOf`.  These are the two shared-leg leg SHAPES that `SpineValleyFrameCollapse`'s
`generalContextFrameLegsCollapse` (LEFT) and `MonotoneFaithful`'s `rightSnakeDoubleWhiskerCollapses` (RIGHT)
collapse to the identity.  So the "2a partner witness" is not a global obstruction — it is this local
factorization, and a `zigZagSharedLeg` redex is ALWAYS a genuine straightenable partner (there is no
"non-partner crossing" hiding at window-distance 1: the boundary coherence forbids it).

## What this does NOT close (gates stay `false`)

This ships the LOCAL factorization (the leg SHAPE).  It does NOT itself assemble the merged-`atomFrame` →
iterated-leg cast bridge (the `composePath`-associativity boundary transport lifting these path equalities into
`atomFrame cupAtom ⊟ atomFrame capAtom ≈ id`), nor the delete-chain-surgery `next`, nor the dispatch swap.  No
gate flag flips; `convOfMapEq` and the fib-3 gate flags stay `false`.  This brick reads NO `matchingOf` /
`partnerIndexOf` / arc structure — it is pure seed-rigidity path algebra.

Raw Lean 4 + Init; the dichotomy is truncated-subtraction `Nat`, the factorizations are `congrArg length` +
`length_composePath` + `adjunctionPath_eq_of_length_eq`; hand-rolled `natAddLeftCancel` (core `Nat.add_left_cancel`
leaks propext).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Clean `Nat` left-cancellation (core `Nat.add_left_cancel` leaks propext) -/

/-- Left-cancellation for `Nat` addition, hand-rolled propext-free (mirror of the COMMUTE producer's helper). -/
private theorem natAddLeftCancelFactor (base : Nat) :
    ∀ {leftValue rightValue : Nat},
      base + leftValue = base + rightValue → leftValue = rightValue := by
  induction base with
  | zero =>
      intro leftValue rightValue sumsEqual
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | succ basePred inductionHypothesis =>
      intro leftValue rightValue sumsEqual
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact inductionHypothesis (Nat.succ.inj sumsEqual)

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free; core `Nat.add_sub_cancel_left`
leaks propext). -/
private theorem natAddSubCancelLeftFactor : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftFactor base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free; core `Nat.sub_eq_zero_of_le` leaks). -/
private theorem natSubAddRightFactor : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightFactor base tail

/-! ## The width dichotomy from the `zigZagSharedLeg` verdict -/

/-- The classifier's `zigZagSharedLeg` verdict is exactly `natWindowDistance = 1`.  Cased on the distance value:
the `0` and `≥ 2` cases produce a different constructor, refuted by `noConfusion`. -/
theorem natWindowDistance_eq_one_of_zigZag
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
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

/-- ★ **The width dichotomy.**  A `zigZagSharedLeg` pair's two left-context widths differ by exactly one, so the
pair is one of the two handednesses: `cupLeft + 1 = capLeft` (LEFT snake) or `capLeft + 1 = cupLeft` (RIGHT
snake).  Pure `Nat`: `(a − b) + (b − a) = 1` with one summand zero forces the successor relation on the other. -/
theorem zigZagSharedLeg_widthDichotomy
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.zigZagSharedLeg) :
    cupAtom.leftContext.length + 1 = capAtom.leftContext.length
      ∨ capAtom.leftContext.length + 1 = cupAtom.leftContext.length := by
  have distanceOne := natWindowDistance_eq_one_of_zigZag cupAtom capAtom verdict
  dsimp only [natWindowDistance] at distanceOne
  rcases Nat.le_total cupAtom.leftContext.length capAtom.leftContext.length with cupLe | capLe
  · left
    obtain ⟨gap, gapEq⟩ := Nat.le.dest cupLe
    rw [← gapEq, natSubAddRightFactor, natAddSubCancelLeftFactor, Nat.zero_add] at distanceOne
    rw [← gapEq, distanceOne]
  · right
    obtain ⟨gap, gapEq⟩ := Nat.le.dest capLe
    rw [← gapEq, natSubAddRightFactor, natAddSubCancelLeftFactor, Nat.add_zero] at distanceOne
    rw [← gapEq, distanceOne]

/-! ## The shared-leg factorization (both handednesses), from the boundary word + width relation -/

/-- ★ **Handedness A (LEFT snake) — the shared-leg factorization.**  For a cup·cap pair whose boundary word
`lcCup · (L·R) · rcCup = lcCap · (R·L) · rcCap` matches and whose cup left context is one shorter than the cap's,
seed rigidity forces `lcCap = lcCup · L` and `rcCup = L · rcCap` — the cap left context extends the cup's by the
shared leg `left`, and the cup right context prepends that same leg onto the cap's.  This is the genuine
non-crossing partner in the LEFT-snake orientation, read off LENGTHS ALONE (no arc structure). -/
theorem sharedLegFactorHandednessA
    {overallSource overallTarget : AdjunctionMode}
    (lcCup : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rcCup : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget)
    (lcCap : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rcCap : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget)
    (coherence : composePath lcCup (composePath adjunctionLeftThenRight rcCup)
      = composePath lcCap (composePath adjunctionRightThenLeft rcCap))
    (widthRel : lcCup.length + 1 = lcCap.length) :
    lcCap = composePath lcCup (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left)
      ∧ rcCup = composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left) rcCap := by
  have leftLength :
      lcCap.length
        = (composePath lcCup (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left)).length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length, ← widthRel]
  have leftEq := adjunctionPath_eq_of_length_eq lcCap
    (composePath lcCup (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left)) leftLength
  have wordLength := congrArg ModalityPath.length coherence
  rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
      ModalityPath.length_composePath, ModalityPath.length_composePath] at wordLength
  rw [← widthRel] at wordLength
  have rightLength : rcCup.length
      = (composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left) rcCap).length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length]
    have cancelable : lcCup.length + (2 + rcCup.length)
        = lcCup.length + (2 + (1 + rcCap.length)) := by
      show lcCup.length + (adjunctionLeftThenRight.length + rcCup.length)
        = lcCup.length + (2 + (1 + rcCap.length))
      rw [wordLength]
      show (lcCup.length + 1) + (adjunctionRightThenLeft.length + rcCap.length)
        = lcCup.length + (2 + (1 + rcCap.length))
      rw [Nat.add_assoc lcCup.length 1 (adjunctionRightThenLeft.length + rcCap.length)]
      show lcCup.length + (1 + (2 + rcCap.length)) = lcCup.length + (2 + (1 + rcCap.length))
      rw [Nat.add_comm 1 (2 + rcCap.length), Nat.add_assoc 2 rcCap.length 1,
          Nat.add_comm rcCap.length 1]
    have cancelTwo := natAddLeftCancelFactor lcCup.length cancelable
    exact natAddLeftCancelFactor 2 cancelTwo
  have rightEq := adjunctionPath_eq_of_length_eq rcCup
    (composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.left) rcCap) rightLength
  exact ⟨leftEq, rightEq⟩

/-- ★ **Handedness B (RIGHT snake) — the mirror shared-leg factorization.**  When the cup left context is one
LONGER than the cap's, seed rigidity forces `lcCup = lcCap · R` and `rcCap = R · rcCup` — the genuine non-crossing
partner in the RIGHT-snake orientation. -/
theorem sharedLegFactorHandednessB
    {overallSource overallTarget : AdjunctionMode}
    (lcCup : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rcCup : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget)
    (lcCap : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rcCap : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget)
    (coherence : composePath lcCup (composePath adjunctionLeftThenRight rcCup)
      = composePath lcCap (composePath adjunctionRightThenLeft rcCap))
    (widthRel : lcCap.length + 1 = lcCup.length) :
    lcCup = composePath lcCap (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right)
      ∧ rcCap = composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right) rcCup := by
  have leftLength :
      lcCup.length
        = (composePath lcCap (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right)).length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length, ← widthRel]
  have leftEq := adjunctionPath_eq_of_length_eq lcCup
    (composePath lcCap (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right)) leftLength
  have wordLength := congrArg ModalityPath.length coherence
  rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
      ModalityPath.length_composePath, ModalityPath.length_composePath] at wordLength
  rw [← widthRel] at wordLength
  have rightLength : rcCap.length
      = (composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right) rcCup).length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length]
    have cancelable : lcCap.length + (2 + (1 + rcCup.length))
        = lcCap.length + (2 + rcCap.length) := by
      show lcCap.length + (2 + (1 + rcCup.length))
        = lcCap.length + (adjunctionRightThenLeft.length + rcCap.length)
      rw [← wordLength]
      show lcCap.length + (2 + (1 + rcCup.length))
        = (lcCap.length + 1) + (adjunctionLeftThenRight.length + rcCup.length)
      rw [Nat.add_assoc lcCap.length 1 (adjunctionLeftThenRight.length + rcCup.length)]
      show lcCap.length + (2 + (1 + rcCup.length)) = lcCap.length + (1 + (2 + rcCup.length))
      rw [Nat.add_comm 1 (2 + rcCup.length), Nat.add_assoc 2 rcCup.length 1,
          Nat.add_comm rcCup.length 1]
    have cancelTwo := natAddLeftCancelFactor lcCap.length cancelable
    exact (natAddLeftCancelFactor 2 cancelTwo).symm
  have rightEq := adjunctionPath_eq_of_length_eq rcCap
    (composePath (singletonModalityPath (graph := adjunctionGraph) AdjunctionModality.right) rcCup) rightLength
  exact ⟨leftEq, rightEq⟩

/-! ## The deletion reconnects the chain (endpoint identification) -/

/-- A genuine cap atom has target arity `0` — the counit `R·L ⟹ id_tip` produces nothing.  Read off the cap tag
by casing the generator: `counit` gives the empty codomain; `unit` (source width `0`) contradicts the cap tag. -/
theorem capAtom_generatorCod_length_zero
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCap : atom.isCupAtom = false) : atom.generatorCod.length = 0 := by
  obtain ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator, rightContext⟩ := atom
  cases generator with
  | unit => nomatch isCap
  | counit => rfl

/-- ★ **A `zigZagSharedLeg` deletion reconnects the chain.**  For a cup·cap pair with matching inter-atom boundary
`atomFrameTarget cupAtom = atomFrameSource capAtom`, the cup's frame SOURCE equals the cap's frame TARGET —
`atomFrameSource cupAtom = atomFrameTarget capAtom` — so deleting the collapsing pair splices the chain back
together (the atoms before the cup meet the atoms after the cap at a common 1-cell).  A pure LENGTH identity: the
cup's empty generator source and the cap's empty generator codomain strip the width-2 windows off both sides of
the boundary coherence, leaving `lcCup · rcCup = lcCap · rcCap`, then seed rigidity closes it.  General (any
matching cup·cap), local, no arc read.  This is the endpoint identification the STRAIGHTEN delete-chain-surgery
consumes to build the post-deletion cell. -/
theorem cupCapDeletionReconnects
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coherence : atomFrameTarget cupAtom = atomFrameSource capAtom) :
    atomFrameSource cupAtom = atomFrameTarget capAtom := by
  have wordLength := congrArg ModalityPath.length coherence
  dsimp only [atomFrameTarget, atomFrameSource] at wordLength
  rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
      ModalityPath.length_composePath, ModalityPath.length_composePath,
      cupAtom_generatorCod_length_two cupAtom isCup,
      capAtom_generatorDom_length_two capAtom isCap] at wordLength
  -- wordLength : lcCup + (2 + rcCup) = lcCap + (2 + rcCap)
  have goalLength : (atomFrameSource cupAtom).length = (atomFrameTarget capAtom).length := by
    dsimp only [atomFrameSource, atomFrameTarget]
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath,
        cupAtom_generatorDom_length_zero cupAtom isCup, Nat.zero_add,
        capAtom_generatorCod_length_zero capAtom isCap, Nat.zero_add]
    -- goal : lcCup + rcCup = lcCap + rcCap
    have shifted : (cupAtom.leftContext.length + cupAtom.rightContext.length) + 2
        = (capAtom.leftContext.length + capAtom.rightContext.length) + 2 := by
      rw [Nat.add_assoc cupAtom.leftContext.length cupAtom.rightContext.length 2,
          Nat.add_comm cupAtom.rightContext.length 2,
          Nat.add_assoc capAtom.leftContext.length capAtom.rightContext.length 2,
          Nat.add_comm capAtom.rightContext.length 2]
      exact wordLength
    have commuted : 2 + (cupAtom.leftContext.length + cupAtom.rightContext.length)
        = 2 + (capAtom.leftContext.length + capAtom.rightContext.length) := by
      rw [Nat.add_comm 2 (cupAtom.leftContext.length + cupAtom.rightContext.length),
          Nat.add_comm 2 (capAtom.leftContext.length + capAtom.rightContext.length)]
      exact shifted
    exact natAddLeftCancelFactor 2 commuted
  exact adjunctionPath_eq_of_length_eq (atomFrameSource cupAtom) (atomFrameTarget capAtom) goalLength

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the STRAIGHTEN 2a "partner witness" is LOCAL, not a global `matchingOf` read.**  A
`zigZagSharedLeg` redex's two left-context widths differ by exactly one (`zigZagSharedLeg_widthDichotomy`), and in
either handedness the inter-atom boundary coherence FORCES the shared-leg factorization by seed rigidity ALONE:
`lcCap = lcCup · L` ∧ `rcCup = L · rcCap` (LEFT snake, `sharedLegFactorHandednessA`) or `lcCup = lcCap · R` ∧
`rcCap = R · rcCup` (RIGHT snake, `sharedLegFactorHandednessB`).  These are exactly the leg SHAPES the shipped
`generalContextFrameLegsCollapse` (LEFT) / `rightSnakeDoubleWhiskerCollapses` (RIGHT) collapse to the identity.
So there is NO "non-partner crossing" at window-distance 1 — the boundary coherence excludes it — and the descent
step never consults `matchingOf`: partner-hood is READ OFF the local geometry, matching the RV/FM verdict.

  The deletion RECONNECTS the chain (`cupCapDeletionReconnects`: `atomFrameSource cupAtom = atomFrameTarget
  capAtom`) — the endpoint identification the delete-chain-surgery consumes, likewise local (a pure length
  identity from the cup/cap arities + boundary coherence, seed rigidity).

  What this marker does NOT close (gates stay `false`): the merged-`atomFrame` → iterated-leg cast bridge (the
  `composePath`-associativity boundary transport turning these path equalities into `atomFrame cupAtom ⊟
  atomFrame capAtom ≈ id`), the delete-chain-surgery `next` cell, and the dispatch swap.  `convOfMapEq` and the
  fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenFactor : Bool := true

end FX1Poly.Polygraph
