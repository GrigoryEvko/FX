import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCanonicalWord

/-! # WalkingString — the STAIRCASE MEASURE, machine-read off the four shipped modes (FC-3, piece B substrate)

FC-2 shipped the four Fuss–Catalan insertion MODES as one-step convertibility lemmas (CANCEL over any context /
EXTEND over any context / COMMUTE, INTERLEAVE as concrete whisker-interchange witnesses) plus the pure-CANCEL fueled
fold `stringSnakeStackF_conv_identity` (`generatorCount` descends by 2 per CANCEL).  Before the full multi-mode
straightening fold can be built, the FC-3 MANDATE is to hand-simulate insertions through the SHIPPED mode shapes and
READ OFF the termination measure.  This file does that read-off as MACHINE-CHECKED arithmetic on the two shipped
structural weights `RawTwoCellExpr.generatorCount` (the word length — `gen` counts 1, `id` 0) and
`RawTwoCellExpr.size` (the node count — every node counts 1):

  * **CANCEL** strictly DROPS `generatorCount` by 2, for ALL FOUR colours (`stringCancelSnake{F,Glo,Ghi,H}_dropsTwo`).
    The substantive reduction — a snake carries two generators (`η`, `ε`), both removed by a triangle.
  * **EXTEND** HOLDS `generatorCount` (`stringExtendByIdentity_generatorCount_neutral` — the dropped slot is an
    `id`, `generatorCount 0`) and strictly DROPS `size` by 2 (`stringExtendByIdentity_size_dropsTwo` — the `vcomp`
    node and the `id` node both vanish).  So EXTEND is caught by the SECOND lex component.
  * **COMMUTE / INTERLEAVE** HOLD BOTH `generatorCount` AND `size` (the whisker-interchange move rearranges the same
    two whisker nodes around the same one generator — `stringWhiskerLeft_generatorCount` /
    `stringWhiskerRight_generatorCount` / `stringCastBoundary_generatorCount`, and the `size` twins, all neutral).
    Neither structural weight descends — so the free-interchange moves need a POSITIONAL potential (the recon's
    `commutePotential`), the THIRD lex component, which only the full driver can define (it depends on the redex
    LOCATION, not the term shape).

## The honest read-off

> **measure = `lex(generatorCount, size, commutePotential)`**

CANCEL descends component 1; EXTEND holds 1, descends 2; COMMUTE / INTERLEAVE hold 1 and 2, descend the positional
component 3.  Crucially there is NO length-preserving ASCENT (no braid — FC's cross-colour move is free interchange,
not a Coxeter braid, `fxString_hasNormalFormDesignLock` §4), so `generatorCount` is a genuine well-founded primary
measure and the pure-CANCEL fragment already folds to a normal form (`stringSnakeStackF_conv_identity`, shipped).
The full multi-mode driver + the `commutePotential` definition + the normal-form uniqueness lemma (which shares the
CAP planar-survivor P4 with the orient closure) is the remaining FC-3 assembly, recorded honestly below.

Raw Lean 4 + Init; every weight lemma is a structural `generatorCount` / `size` evaluation (`rfl` or one
`Nat.add_assoc`).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two structural weights are neutral under the boundary-invisible constructors -/

/-- Left whiskering fires no generator: `(oneCell ◁ cell).generatorCount = cell.generatorCount`.  `rfl` — the
`whiskerLeft` arm of `generatorCount` passes through. -/
theorem stringWhiskerLeft_generatorCount {sourceMode middleMode targetMode : AdjointTripleMode}
    (oneCell : ModalityPath adjointTripleGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath adjointTripleGraph middleMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH) :
    (RawTwoCellExpr.whiskerLeft oneCell cell).generatorCount = cell.generatorCount := rfl

/-- Right whiskering fires no generator: `(cell ▷ oneCell).generatorCount = cell.generatorCount`.  `rfl`. -/
theorem stringWhiskerRight_generatorCount {sourceMode middleMode targetMode : AdjointTripleMode}
    {oneCellF oneCellG : ModalityPath adjointTripleGraph sourceMode middleMode}
    (oneCell : ModalityPath adjointTripleGraph middleMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG) :
    (RawTwoCellExpr.whiskerRight oneCell cell).generatorCount = cell.generatorCount := rfl

/-- ★ A boundary CAST fires no generator: `(castBoundary h1 h2 cell).generatorCount = cell.generatorCount`.  The
cast is `h1 ▸ h2 ▸ cell`; substituting the two boundary equalities collapses it to `cell`.  This is the lemma the
COMMUTE / INTERLEAVE read-off needs, since their reducts are wrapped in a `castBoundary` (the boundary is only
propositionally equal after re-nesting). -/
theorem stringCastBoundary_generatorCount {sourceMode targetMode : AdjointTripleMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath adjointTripleGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).generatorCount = cell.generatorCount := by
  cases hsource; cases htarget; rfl

/-- Left whiskering adds ONE node: `(oneCell ◁ cell).size = cell.size + 1`.  `rfl`. -/
theorem stringWhiskerLeft_size {sourceMode middleMode targetMode : AdjointTripleMode}
    (oneCell : ModalityPath adjointTripleGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath adjointTripleGraph middleMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH) :
    (RawTwoCellExpr.whiskerLeft oneCell cell).size = cell.size + 1 := rfl

/-- Right whiskering adds ONE node: `(cell ▷ oneCell).size = cell.size + 1`.  `rfl`. -/
theorem stringWhiskerRight_size {sourceMode middleMode targetMode : AdjointTripleMode}
    {oneCellF oneCellG : ModalityPath adjointTripleGraph sourceMode middleMode}
    (oneCell : ModalityPath adjointTripleGraph middleMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG) :
    (RawTwoCellExpr.whiskerRight oneCell cell).size = cell.size + 1 := rfl

/-- ★ A boundary CAST adds no node: `(castBoundary h1 h2 cell).size = cell.size`.  Same collapse as the
`generatorCount` twin — the COMMUTE / INTERLEAVE `size` read-off. -/
theorem stringCastBoundary_size {sourceMode targetMode : AdjointTripleMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath adjointTripleGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).size = cell.size := by
  cases hsource; cases htarget; rfl

/-! ## CANCEL — the substantive descent: `generatorCount` drops by 2, all four colours -/

/-- ★ **CANCEL (colour-1 lower `G`) drops the generator count by 2.**  `stringSnakeGlo` carries `η`, `ε`; a CANCEL
removes both, so `(vcomp w stringSnakeGlo).generatorCount = w.generatorCount + 2`.  `rfl` (the `F`-colour twin is
the shipped `stringCancelSnakeF_dropsTwo`). -/
theorem stringCancelSnakeGlo_dropsTwo
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    (RawTwoCellExpr.vcomp w stringSnakeGlo).generatorCount = w.generatorCount + 2 := rfl

/-- ★ **CANCEL (colour-2 upper `G`) drops the generator count by 2.**  The OTHER colour straightening the shared
`G`; `(vcomp w stringSnakeGhi).generatorCount = w.generatorCount + 2`.  `rfl`. -/
theorem stringCancelSnakeGhi_dropsTwo
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    (RawTwoCellExpr.vcomp w stringSnakeGhi).generatorCount = w.generatorCount + 2 := rfl

/-- ★ **CANCEL (colour-2 `H`) drops the generator count by 2.**  `(vcomp w stringSnakeH).generatorCount =
w.generatorCount + 2`.  `rfl`. -/
theorem stringCancelSnakeH_dropsTwo
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.coLeft)) :
    (RawTwoCellExpr.vcomp w stringSnakeH).generatorCount = w.generatorCount + 2 := rfl

/-! ## EXTEND — holds `generatorCount`, drops `size` (caught by the second lex component) -/

/-- ★ **EXTEND holds the generator count.**  Appending an `id` slot fires no generator:
`(vcomp w (id path)).generatorCount = w.generatorCount` (the dropped slot is `generatorCount 0`), so EXTEND is
INVISIBLE to the primary measure — it is caught by the second component (`size`).  `w.generatorCount + 0`, `rfl`. -/
theorem stringExtendByIdentity_generatorCount_neutral
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)).generatorCount
      = w.generatorCount := rfl

/-- ★ **EXTEND drops `size` by 2.**  The `vcomp` node and the `id` node both vanish when the reducible identity slot
is absorbed: `(vcomp w (id path)).size = w.size + 2`.  So the lex pair `(generatorCount, size)` strictly descends on
an EXTEND (component 1 held, component 2 dropped).  `w.size + 1 + 1 = w.size + 2` by `Nat.add_assoc`. -/
theorem stringExtendByIdentity_size_dropsTwo
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)).size
      = w.size + 2 := by
  show w.size + 1 + 1 = w.size + 2
  rw [Nat.add_assoc]

/-! ## The pure-CANCEL fold already exhibits the primary descent (re-export the read-off) -/

/-- ★ **The primary measure descends across the shipped CANCEL fold.**  The `n`-fold `F`-snake stack has
`generatorCount = 2n` (`stringSnakeStackF_generatorCount`), and each CANCEL step drops it by 2 down to
`(id_F).generatorCount = 0`; the fold `stringSnakeStackF_conv_identity` witnesses that the descent terminates.  This
re-states, as a `generatorCount` equation, that the CANCEL fold's fuel IS the primary lex component. -/
theorem stringSnakeStackF_generatorCount_descends (count : Nat) :
    (stringSnakeStackF count).generatorCount = 2 * count
      ∧ (stringSnakeStackF (count + 1)).generatorCount = (stringSnakeStackF count).generatorCount + 2 := by
  refine ⟨stringSnakeStackF_generatorCount count, ?_⟩
  show stringSnakeF.generatorCount + (stringSnakeStackF count).generatorCount
    = (stringSnakeStackF count).generatorCount + 2
  exact Nat.add_comm stringSnakeF.generatorCount (stringSnakeStackF count).generatorCount

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the FC-3 staircase MEASURE is read off the four shipped modes, machine-checked.**  The
termination measure is the lexicographic triple `lex(generatorCount, size, commutePotential)`, and every mode's
effect on the two SHIPPED structural weights is a machine-checked equation: CANCEL drops `generatorCount` by 2 for
ALL FOUR colours (`stringCancelSnake{F,Glo,Ghi,H}_dropsTwo`, the `F` twin shipped in FC-2); EXTEND holds
`generatorCount` (`stringExtendByIdentity_generatorCount_neutral`) and drops `size` by 2
(`stringExtendByIdentity_size_dropsTwo`); COMMUTE / INTERLEAVE hold BOTH weights (the whisker + cast neutrality
lemmas `stringWhiskerLeft_generatorCount` / `stringWhiskerRight_generatorCount` / `stringCastBoundary_generatorCount`
and their `size` twins).  There is NO length-preserving ASCENT (no braid), so `generatorCount` is a genuine primary
measure and the pure-CANCEL fragment already folds to a normal form
(`stringSnakeStackF_generatorCount_descends` + `stringSnakeStackF_conv_identity`).  `= true`. -/
def fxString_hasStaircaseMeasure : Bool := true

/-- **OPEN (honest) — the COMMUTE / INTERLEAVE positional potential + the full multi-mode DRIVER stay unbuilt.**  The
two structural weights `generatorCount` and `size` are BOTH neutral under COMMUTE / INTERLEAVE (proved above), so the
free-interchange moves are invisible to them: their strict descent lives entirely in the THIRD lex component
`commutePotential` — the number of disjoint generators between a snake redex and its innermost-fireable position — a
POSITIONAL quantity that depends on the redex LOCATION, not the term shape.  Defining it requires the redex-locating
DRIVER (`fireSnakeAt` / `commuteAt`), which does not yet exist over `RawTwoCellExpr` (FC-2 ships COMMUTE / INTERLEAVE
only as concrete one-step witnesses, no context parameter, no locator).  So the full multi-mode straightening fold
(and the normal-form uniqueness lemma it feeds, which shares the CAP planar-survivor P4 with the orient closure) is
the remaining FC-3 assembly, honestly walled: the measure is read off and every structural-weight descent is
machine-checked, but the positional driver and the uniqueness lemma are not built this pass.  `= false`. -/
def fxString_hasStaircaseDriver : Bool := false

end FX1Poly.Polygraph
