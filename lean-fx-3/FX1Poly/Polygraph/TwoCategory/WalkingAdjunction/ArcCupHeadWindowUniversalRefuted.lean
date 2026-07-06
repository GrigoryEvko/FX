import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # ArcCupHeadWindowUniversalRefuted — the head-cup window is NOT a universal function of the arc structure

`ArcCupHeadWindowSeparation` shipped an EXISTENTIAL separation (ANGLE B): the two witnesses
`spineHeadWindowZero` / `spineHeadWindowTwo` — head cups at windows `0` vs `2` over the bottom boundary
`L·R` — share the whole boundary `DiagramType` and the cup/cap totals yet differ in `internalCupCounts`
(`[1,0,1,0]` vs `[0,1,0,1]`).  That witness LEFT OPEN the decisive R1c question: is the head-cup window a
**universal** function of the arc structure (so `windowPin` would be a readoff off `internalCupCounts`), or
only existentially separated on that one witness?

This file settles it with a **machine-checked COUNTEREXAMPLE**: the head-cup window is NOT a universal
function of the arc structure.  Two boundary-chained, cup-headed spines at boundary `2` whose head cups sit
at DIFFERENT windows (`0` vs `2`) have the SAME `FullArcStructure` — same `diagram` (partner
`[4,5,3,2,0,1,7,6]`), same totals, and the SAME `internalCupCounts` (`[0,0,1,1,0,0,1,1]`).  So no field of
the arc structure — the boundary matching NOR `internalCupCounts` — recovers the head window in general.

## The mechanism (why the ANGLE-B separation does not generalize)

The two spines are the two interleavings of TWO horizontally-independent unit cups over the `L·R` strand —
one seated at the FRONT (window `0`), one at the BACK (window `2` / `4`) — realized by the genuine parallel
cells `orbitCellHeadFront` / `orbitCellHeadBack` (`: L·R ⇒ L·R·L·R·L·R`, spines `orbitSpineHeadFront` /
`orbitSpineHeadBack` on the nose).  They are trace-equivalent (a single interchange of the two independent
cups), so — the arc structure being trace-invariant — they MUST share it, and they DO.  Reordering the two
independent cups puts a DIFFERENT cup at the head, with a DIFFERENT window, while the arc structure is fixed.
The ANGLE-B witness avoided this only because its two cups were COUPLED by a connecting cap (so no independent
reordering existed); with two genuinely independent cups the window collapses.

## What this settles for the cup-head crux (`windowPin`)

`windowPin` (`movedTarget.leftContext.length = headAtom.leftContext.length`) is NOT a readoff from any arc
field — it is genuine ORBIT content, exactly as `ArcCupReselectionOrbit`'s ANGLE-C argued.  A cup CREATES two
fresh legs and consumes no bottom port, so its window has no bottom-boundary anchor; it survives only as a
choice of trace-orbit REPRESENTATIVE.  Hence the surviving route for the cup case is the leg-aligned
re-selection `arcCupReselection_exists` (which CHOOSES the representative with the head cup at the front at its
window), NOT a readoff off `internalCupCounts`.  This file KILLS the readoff route and CORRECTS the optimistic
framing of `ArcCupHeadWindowSeparation` (whose separation is only existential).  It does NOT refute the arc
RECONSTRUCTION `arcStructureOf a = arcStructureOf b → SpineTraceEquiv a b`: the two witnesses ARE
trace-equivalent, so the reconstruction (the orbit route) is untouched — only the window-as-arc-field readoff dies.

Raw Lean 4 + Init; the arc equality closes by kernel `decide` on the computable arc fold, the chains by
`SpineBoundaryChained.cons`, the readoffs / disequality by `rfl` / `Nat.noConfusion`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open AdjunctionMode AdjunctionModality

/-! ## The two independent-cup witness spines -/

/-- The empty `base ⟶ base` context (window / rest length `0`). -/
def orbitNilBase : ModalityPath adjunctionGraph base base :=
  ModalityPath.nil (graph := adjunctionGraph) base

/-- The length-`2` `base ⟶ base` context `L·R`. -/
def orbitPathLR : ModalityPath adjunctionGraph base base := adjunctionLeftThenRight

/-- The length-`4` `base ⟶ base` context `L·R·L·R`. -/
def orbitPathLRLR : ModalityPath adjunctionGraph base base :=
  composePath adjunctionLeftThenRight adjunctionLeftThenRight

/-- A unit (cup, `0 ⇒ 2`) spine atom over `base ⟶ base` with the given left / right whisker contexts.  Its
window is `leftContext.length`; its dom / cod arities are `0` / `2`. -/
def unitCupAtom (leftContext rightContext : ModalityPath adjunctionGraph base base) :
    SpineAtom adjunctionModeSignature base base where
  leftMidMode := base
  rightMidMode := base
  leftContext := leftContext
  generatorDom := orbitNilBase
  generatorCod := adjunctionLeftThenRight
  generator := AdjunctionTwoCell.unit
  rightContext := rightContext

/-- The FRONT-headed witness: the front cup (window `0`, rest `L·R`) then the back cup (window `4`, rest empty).
Its HEAD cup sits at window `0`. -/
def orbitSpineHeadFront : List (SpineAtom adjunctionModeSignature base base) :=
  [unitCupAtom orbitNilBase orbitPathLR, unitCupAtom orbitPathLRLR orbitNilBase]

/-- The BACK-headed witness: the back cup (window `2`, rest empty) then the front cup (window `0`, rest
`L·R·L·R`).  The SAME two independent cups as `orbitSpineHeadFront`, reordered — so its HEAD cup sits at
window `2`. -/
def orbitSpineHeadBack : List (SpineAtom adjunctionModeSignature base base) :=
  [unitCupAtom orbitPathLR orbitNilBase, unitCupAtom orbitNilBase orbitPathLRLR]

/-! ## Both are boundary-chained cup-headed spines at boundary `2` -/

/-- The front-headed witness is boundary-chained at `2` (widths `2 → 4 → 6`). -/
theorem orbitSpineHeadFront_isChained : SpineBoundaryChained 2 orbitSpineHeadFront :=
  SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))

/-- The back-headed witness is boundary-chained at `2` (widths `2 → 4 → 6`). -/
theorem orbitSpineHeadBack_isChained : SpineBoundaryChained 2 orbitSpineHeadBack :=
  SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))

/-- The front-headed witness's atoms as `(window, dom arity, cod arity)`: a cup at window `0`, then a cup at
window `4`.  Its head is a cup at window `0`. -/
theorem orbitSpineHeadFront_atomReadoff :
    orbitSpineHeadFront.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(0, 0, 2), (4, 0, 2)] := rfl

/-- The back-headed witness's atoms: a cup at window `2`, then a cup at window `0`.  Its head is a cup at
window `2` — differing from the front-headed witness's head ONLY in window. -/
theorem orbitSpineHeadBack_atomReadoff :
    orbitSpineHeadBack.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(2, 0, 2), (0, 0, 2)] := rfl

/-! ## The two arc structures are EQUAL, yet the head windows DIFFER -/

set_option maxHeartbeats 1600000 in
/-- ★ **The two witnesses share the ENTIRE `FullArcStructure`.**  Same `diagram` (partner
`[4,5,3,2,0,1,7,6]`, no loops), same cup/cap totals, and — crucially — the SAME `internalCupCounts`
(`[0,0,1,1,0,0,1,1]`) and `internalCapCounts`.  So NO field of the arc structure separates the two head
windows: the ANGLE-B separation (window `0` vs `2` under a coupling cap) does NOT generalize to two
independent cups. -/
theorem orbitSpines_arcStructure_eq :
    arcStructureOfSpineList 2 orbitSpineHeadFront = arcStructureOfSpineList 2 orbitSpineHeadBack := by
  decide +kernel

/-- The front-headed witness's head cup is a genuine cup: dom arity `0`, cod arity `2`. -/
theorem orbitSpineHeadFront_headIsCup :
    (unitCupAtom orbitNilBase orbitPathLR).generatorDom.length = 0
      ∧ (unitCupAtom orbitNilBase orbitPathLR).generatorCod.length = 2 := ⟨rfl, rfl⟩

/-- The back-headed witness's head cup is a genuine cup: dom arity `0`, cod arity `2`. -/
theorem orbitSpineHeadBack_headIsCup :
    (unitCupAtom orbitPathLR orbitNilBase).generatorDom.length = 0
      ∧ (unitCupAtom orbitPathLR orbitNilBase).generatorCod.length = 2 := ⟨rfl, rfl⟩

/-- ★ **The two head-cup windows DIFFER** (`0 ≠ 2`) — read straight off the two head atoms' left contexts. -/
theorem orbitSpines_headWindows_ne :
    (unitCupAtom orbitNilBase orbitPathLR).leftContext.length
      ≠ (unitCupAtom orbitPathLR orbitNilBase).leftContext.length := fun windowsEqual =>
  Nat.noConfusion windowsEqual

/-! ## The universal head-cup window readoff is FALSE -/

/-- The **universal head-cup window readoff** the cup-head crux would need (`windowPin` promoted to a readoff
off the arc data): over EVERY pair of boundary-chained, cup-headed spines at boundary `boundaryLength`, equal
arc structures force equal head-cup windows. -/
def HeadCupWindowReadoff (boundaryLength : Nat) : Prop :=
  ∀ (headFirst headSecond : SpineAtom adjunctionModeSignature base base)
    (tailFirst tailSecond : List (SpineAtom adjunctionModeSignature base base)),
    SpineBoundaryChained boundaryLength (headFirst :: tailFirst) →
    SpineBoundaryChained boundaryLength (headSecond :: tailSecond) →
    headFirst.generatorDom.length = 0 → headFirst.generatorCod.length = 2 →
    headSecond.generatorDom.length = 0 → headSecond.generatorCod.length = 2 →
    arcStructureOfSpineList boundaryLength (headFirst :: tailFirst)
      = arcStructureOfSpineList boundaryLength (headSecond :: tailSecond) →
    headFirst.leftContext.length = headSecond.leftContext.length

/-- ★ **The universal head-cup window readoff is FALSE at boundary `2`.**  Instantiated on the two
independent-cup witnesses (both boundary-chained and cup-headed, with equal arc structure by
`orbitSpines_arcStructure_eq`), the readoff would force `0 = 2`.  So the head-cup window is NOT a universal
function of the arc structure (in particular not of `internalCupCounts`); it is genuine trace-orbit content.
This is the DECISIVE R1c answer — the ANGLE-B separation is existential only. -/
theorem headCupWindowReadoff_isFalse : ¬ HeadCupWindowReadoff 2 := fun readoff =>
  orbitSpines_headWindows_ne
    (readoff (unitCupAtom orbitNilBase orbitPathLR) (unitCupAtom orbitPathLR orbitNilBase)
      [unitCupAtom orbitPathLRLR orbitNilBase] [unitCupAtom orbitNilBase orbitPathLRLR]
      orbitSpineHeadFront_isChained orbitSpineHeadBack_isChained rfl rfl rfl rfl
      orbitSpines_arcStructure_eq)

/-! ## The witnesses are genuine parallel cells (`L·R ⇒ L·R·L·R·L·R`) -/

/-- The FRONT-headed witness realized as a genuine cell: a unit whiskered at the front of `L·R`, then a unit
whiskered at the back.  Its spine is `orbitSpineHeadFront` on the nose. -/
def orbitCellHeadFront :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight orbitPathLR adjunctionUnitTwoCell)
    (RawTwoCellExpr.whiskerLeft orbitPathLRLR adjunctionUnitTwoCell)

/-- The BACK-headed witness realized as a genuine cell: a unit whiskered at the back of `L·R`, then a unit
whiskered at the front.  The SAME two independent cups as `orbitCellHeadFront`, reordered.  Its spine is
`orbitSpineHeadBack` on the nose. -/
def orbitCellHeadBack :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft orbitPathLR adjunctionUnitTwoCell)
    (RawTwoCellExpr.whiskerRight orbitPathLRLR adjunctionUnitTwoCell)

/-- The front cell's spine is exactly the front-headed witness spine. -/
theorem orbitCellHeadFront_spine : orbitCellHeadFront.spine = orbitSpineHeadFront := rfl

/-- The back cell's spine is exactly the back-headed witness spine. -/
theorem orbitCellHeadBack_spine : orbitCellHeadBack.spine = orbitSpineHeadBack := rfl

/-- ★ **The two genuine parallel cells have equal `arcStructureOf`** (they realize the equal-arc witnesses),
yet their head cups sit at windows `0` and `2` (`orbitCellHeadFront_spine` / `orbitCellHeadBack_spine` +
`orbitSpineHeadFront_atomReadoff` / `orbitSpineHeadBack_atomReadoff`).  So even over GENUINE
(trace-equivalent) cells the head window is arc-invisible. -/
theorem orbitCells_arcStructure_eq :
    arcStructureOf orbitCellHeadFront = arcStructureOf orbitCellHeadBack :=
  orbitSpines_arcStructure_eq

/-! ## Honesty marker -/

/-- **Honesty marker — the head-cup window is NOT a universal function of the arc structure.**  Two
boundary-chained (`orbitSpineHeadFront_isChained` / `orbitSpineHeadBack_isChained`), cup-headed spines at
boundary `2` whose head cups differ ONLY in window (`0` vs `2`, `orbitSpines_headWindows_ne`) share the WHOLE
`FullArcStructure` — diagram, totals, AND `internalCupCounts` — by `orbitSpines_arcStructure_eq`, realized by
the genuine parallel cells `orbitCellHeadFront` / `orbitCellHeadBack` (`orbitCells_arcStructure_eq`).  Hence
the universal readoff `HeadCupWindowReadoff 2` is FALSE (`headCupWindowReadoff_isFalse`).  What this SETTLES
(R1c): the head-cup window is NOT recoverable from any arc field — the `ArcCupHeadWindowSeparation`
`internalCupCounts` separation is EXISTENTIAL only, and `windowPin` is genuine trace-orbit content (the
`ArcCupReselectionOrbit` ANGLE-C position, now machine-checked), so the surviving cup-case route is the
leg-aligned re-selection `arcCupReselection_exists`, NOT an arc-field readoff.  What this marker does NOT
claim: any refutation of the arc RECONSTRUCTION (the two witnesses ARE trace-equivalent, so
`arcStructureOf a = arcStructureOf b → SpineTraceEquiv a b` is untouched) nor `windowPin` itself.  `= true`. -/
def fxMode_hasArcCupHeadWindowUniversalRefuted : Bool := true

end FX1Poly.Polygraph
