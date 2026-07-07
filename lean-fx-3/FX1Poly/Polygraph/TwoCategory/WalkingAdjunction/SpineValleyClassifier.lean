import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionPathRigidity

/-! # mode-3 keystone — Piece I classifier: the commute/straighten dispatch is TOTAL on the two real kinds

`SpineValleyProgress` located an adjacent cup-then-cap pair in a non-valley spine and CLASSIFIED it
(`classifyAdjacentAtoms`) into three kinds by the two atoms' left-context widths: `orientationExcludedBothLegs`
(equal widths), `zigZagSharedLeg` (widths differ by 1), `disjointWindows` (widths differ by ≥ 2).  The tag
driver never needed the classifier — a pure transposition dodges it — but the CELL-level mixed driver must
dispatch straighten-vs-commute per pair, so it needs the third kind proven IMPOSSIBLE (there is no cell move for
it, and it must not block totality).

This file proves that impossibility, and it is a pure LENGTH-PARITY fact — no coherence, no adjacency:

  * ★ **`cupAtom_leftMidMode_isBase` / `capAtom_leftMidMode_isTip`** — in the walking adjunction the only
    generators are `unit` (source width 0 → a cup, endo at `base`) and `counit` (source width 2 → a cap, endo at
    `tip`).  So a cup atom's generator-source mode is `base`, a cap atom's is `tip` — read off by casing the
    generator.
  * ★ **`orientationExcludedBothLegs_impossible`** — a cup atom and a cap atom sharing the same overall source
    have left contexts landing on DIFFERENT modes (`base` vs `tip`), so by seed rigidity
    (`adjunctionPathTargets_eq_of_length_eq`: same source + equal length ⟹ equal target) their left-context
    lengths CANNOT be equal.  Hence `natWindowDistance = 0` is unreachable for a genuine cup-then-cap pair.
  * ★ **`classifyAdjacentAtoms_ne_orientationExcluded`** — therefore the classifier never returns
    `orientationExcludedBothLegs` on a genuine cup-then-cap pair; the cell dispatcher is total on the two real
    kinds (zig-zag → STRAIGHTEN, disjoint → COMMUTE).

Raw Lean 4 + Init; the mode read-off is generator casing, the impossibility is seed rigidity + `base ≠ tip`
`noConfusion`, the `natWindowDistance = 0 → eq` is `Nat.add_eq_zero` + `Nat.le_antisymm` on the truncated
differences.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generator-source mode of a cup / cap atom -/

/-- A cup atom (source width `0`) in the walking adjunction is the `unit`, whose generator-source mode is `base`.
Cased on the generator: `unit` gives `base` by unification; `counit` (source width `2`) contradicts the cup tag. -/
theorem cupAtom_leftMidMode_isBase
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : atom.isCupAtom = true) : atom.leftMidMode = AdjunctionMode.base := by
  obtain ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator, rightContext⟩ := atom
  cases generator with
  | unit => rfl
  | counit => nomatch isCup

/-- A cap atom (source width `≥ 1`) in the walking adjunction is the `counit`, whose generator-source mode is
`tip`.  Cased on the generator: `counit` gives `tip` by unification; `unit` (source width `0`) contradicts the
cap tag. -/
theorem capAtom_leftMidMode_isTip
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCap : atom.isCupAtom = false) : atom.leftMidMode = AdjunctionMode.tip := by
  obtain ⟨leftMidMode, rightMidMode, leftContext, generatorDom, generatorCod, generator, rightContext⟩ := atom
  cases generator with
  | unit => nomatch isCap
  | counit => rfl

/-! ## `natWindowDistance = 0` forces equal widths -/

/-- The truncated-difference window distance is `0` exactly when the two widths agree: `(a - b) + (b - a) = 0`
gives `a - b = 0` and `b - a = 0`, hence `a ≤ b` and `b ≤ a`. -/
theorem natWindowDistance_eq_zero_imp_eq (leftLen rightLen : Nat)
    (isZero : natWindowDistance leftLen rightLen = 0) : leftLen = rightLen := by
  dsimp only [natWindowDistance] at isZero
  obtain ⟨leftSubZero, rightSubZero⟩ := Nat.add_eq_zero_iff.mp isZero
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero leftSubZero) (Nat.le_of_sub_eq_zero rightSubZero)

/-! ## The both-legs case is orientation-excluded -/

/-- ★ **The `orientationExcludedBothLegs` geometry is impossible.**  A genuine cup-then-cap pair over one overall
source cannot have equal left-context widths: the cup's left context lands on `base`, the cap's on `tip`, but by
seed rigidity two paths from the same source with equal length land on the SAME mode — and `base ≠ tip`. -/
theorem orientationExcludedBothLegs_impossible
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false) :
    cupAtom.leftContext.length ≠ capAtom.leftContext.length := by
  intro lengthsEqual
  have modesEqual : cupAtom.leftMidMode = capAtom.leftMidMode :=
    adjunctionPathTargets_eq_of_length_eq cupAtom.leftContext capAtom.leftContext lengthsEqual
  rw [cupAtom_leftMidMode_isBase cupAtom isCup, capAtom_leftMidMode_isTip capAtom isCap] at modesEqual
  exact AdjunctionMode.noConfusion modesEqual

/-- ★ **The classifier never returns `orientationExcludedBothLegs` on a genuine cup-then-cap pair.**  So the
cell-level dispatcher is TOTAL on the two real kinds (zig-zag → STRAIGHTEN, disjoint → COMMUTE): if the classifier
landed on the both-legs case the widths would be equal (`natWindowDistance = 0`), refuted above. -/
theorem classifyAdjacentAtoms_ne_orientationExcluded
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false) :
    classifyAdjacentAtoms cupAtom capAtom ≠ AdjacentCupCapKind.orientationExcludedBothLegs := by
  intro classifiedBothLegs
  apply orientationExcludedBothLegs_impossible cupAtom capAtom isCup isCap
  apply natWindowDistance_eq_zero_imp_eq
  cases isDistance :
      natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length with
  | zero => rfl
  | succ predDistance =>
      exfalso
      rw [classifyAdjacentAtoms, classifyAdjacentCupCap, isDistance] at classifiedBothLegs
      cases predDistance with
      | zero => exact AdjacentCupCapKind.noConfusion classifiedBothLegs
      | succ _ => exact AdjacentCupCapKind.noConfusion classifiedBothLegs

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the commute/straighten classifier is TOTAL on the two real kinds; the
`orientationExcludedBothLegs` case is proven IMPOSSIBLE.**  A genuine cup-then-cap pair has its cup left context
land on `base` and its cap left context on `tip` (`cupAtom_leftMidMode_isBase` / `capAtom_leftMidMode_isTip`,
cased off the two seed generators); seed rigidity then forbids equal left-context widths
(`orientationExcludedBothLegs_impossible`), so the classifier never returns the both-legs kind
(`classifyAdjacentAtoms_ne_orientationExcluded`).  The cell dispatcher may therefore treat only ZIG-ZAG →
STRAIGHTEN and DISJOINT → COMMUTE, discharging the third constructor by absurdity.

  What this marker does NOT close: the dispatcher itself (the `SaturatedTwoCellConv`-valued mixed driver
  consuming this classifier), the realization exhibiting the located split as a `vcomp` readback shape, nor the
  reduction to Piece II.  This is a case-totality lemma; it flips no gate.  `= true`. -/
def fxMode_hasSpineValleyClassifierTotality : Bool := true

end FX1Poly.Polygraph
