import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeel
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # mode-3 floor — the arc peel's ARITY CEILING, with a concrete crossing witness

`FreeTwoCellArcGodementSoundnessPeel` closed the Godement arc soundness at the walking adjunction (non-empty
boundary) by firing `extractArc_eq_of_atomicTraceEquiv` — the shipped peel whose swap dispatcher
(`arcSwapCorePackage_of_adjunctionSwap`) is `adjunctionModeSignature`-hardcoded through an EXHAUSTIVE
two-constructor case split on `{unit, counit}` = `{cup 0⇒2, cap 2⇒0}`.  Its wall marker
`fxMode_hasArcGodementSoundnessPeelEmptyBoundary` records the peel is "off the walking adjunction" walled.  This
file makes that wall's SECOND clause — the signature ceiling — a machine-witness rather than a prose claim.

  ★ The arc fold's cup/cap EVENT stream — the data the peel dispatches on — is BLIND to any generator whose
    arity is not `0⇒2` or `2⇒0`: a `2⇒2` crossing takes `stepArcAtom`'s generic-box arm, recording NEITHER a
    cup event NOR a cap event (`crossAtom_stepArcAtom_recordsNoCupEvent` / `_recordsNoCapEvent`, both `rfl` — the
    concrete arities reduce the `stepArcAtom` match to its box arm for every state).
  ★ The walking adjunction has ONLY cup/cap atoms (`adjunctionSpineAtom_hasCupOrCapArity`, shipped), so the box
    arm never fires at the seed — the peel's four builders are exhaustive THERE.
  ★ A general signature is NOT so restricted: the toy one-object `crossModeSignature` carries a `2⇒2` crossing
    generator whose spine atom `crossAtom` is NOT `AtomHasCupOrCapArity` (`crossAtom_isNotCupOrCap`) — the
    concrete general-signature word with a crossing the peel's four cup/cap builders do NOT cover.

So the peel's arity-lock is ESSENTIAL, not incidental: at `{0⇒2, 2⇒0}` the four builders
`arcSwapCorePackage_{cupCup, cupCap, capCup, capCap}` are exhaustive; at a `2⇒2` (or any non-cup/cap) generator
there is no builder arm, and the general-signature peel `ArcGodementSamePartitionFresh signature` stays the open
keystone (`fxMode_hasArcGodementSamePartitionFreshProof`).  This is the ceiling CHARACTERIZATION; it does NOT
claim the general peel is impossible (it is provable — just equal to grinding the keystone, out of scope for one
round), only that the adjunction-hardcoded dispatcher does not reach it.

Raw Lean 4 + Init; the toy signature is a one-object quiver with a single endo-modality and a single `2⇒2`
generator; the box-arm facts are `rfl`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A toy one-object signature carrying a 2⇒2 crossing generator -/

/-- The single mode of the crossing toy signature. -/
inductive CrossMode where
  /-- The only object. -/
  | dot

/-- The single endo-modality `dot ⟶ dot` (a strand). -/
inductive CrossModality : CrossMode → CrossMode → Type where
  /-- The strand `dot ⟶ dot`. -/
  | strand : CrossModality CrossMode.dot CrossMode.dot

/-- The one-object quiver with a single endo-strand. -/
def crossGraph : ModeGraph where
  Mode := CrossMode
  Modality := CrossModality

/-- The width-2 free 1-cell `strand · strand` — the crossing's boundary. -/
def crossStrandPair : ModalityPath crossGraph CrossMode.dot CrossMode.dot :=
  ModalityPath.cons CrossModality.strand
    (ModalityPath.cons CrossModality.strand (ModalityPath.nil (graph := crossGraph) CrossMode.dot))

/-- The single generating 2-cell: a `2⇒2` crossing `strand·strand ⟹ strand·strand`. -/
inductive CrossTwoCell :
    {sourceMode targetMode : CrossMode} →
    ModalityPath crossGraph sourceMode targetMode →
    ModalityPath crossGraph sourceMode targetMode → Type where
  /-- The crossing (braid) generator. -/
  | cross : CrossTwoCell crossStrandPair crossStrandPair

/-- The toy crossing signature: one object, one endo-strand, one `2⇒2` crossing generator. -/
def crossModeSignature : ModeSignature where
  graph := crossGraph
  twoCell := fun firstPath secondPath => CrossTwoCell firstPath secondPath

/-- The spine atom of the bare crossing (no whisker context) — a `2⇒2` generator firing at position `0`. -/
def crossAtom : SpineAtom crossModeSignature CrossMode.dot CrossMode.dot where
  leftMidMode := CrossMode.dot
  rightMidMode := CrossMode.dot
  leftContext := ModalityPath.nil (graph := crossGraph) CrossMode.dot
  generatorDom := crossStrandPair
  generatorCod := crossStrandPair
  generator := CrossTwoCell.cross
  rightContext := ModalityPath.nil (graph := crossGraph) CrossMode.dot

/-- The crossing's domain boundary has width `2`. -/
theorem crossAtom_generatorDom_length : crossAtom.generatorDom.length = 2 := rfl

/-- The crossing's codomain boundary has width `2`. -/
theorem crossAtom_generatorCod_length : crossAtom.generatorCod.length = 2 := rfl

/-! ## The crossing is invisible to the cup/cap event stream -/

/-- ★ **A `2⇒2` crossing records NO cup event.**  `stepArcAtom` on `crossAtom` takes the generic-box arm (its
arity is neither `0⇒2` nor `2⇒0`), which leaves `cupEventNodes` untouched — `rfl` (the concrete arities reduce
the `stepArcAtom` match to its box arm for every state). -/
theorem crossAtom_stepArcAtom_recordsNoCupEvent (state : ArcWireState) :
    (stepArcAtom state crossAtom).cupEventNodes = state.cupEventNodes := rfl

/-- ★ **A `2⇒2` crossing records NO cap event.**  The dual of `crossAtom_stepArcAtom_recordsNoCupEvent`. -/
theorem crossAtom_stepArcAtom_recordsNoCapEvent (state : ArcWireState) :
    (stepArcAtom state crossAtom).capEventNodes = state.capEventNodes := rfl

/-- ★ **The crossing is NOT a cup or a cap.**  `AtomHasCupOrCapArity crossAtom` would force its arity to be
`0⇒2` or `2⇒0`; it is `2⇒2`, so both disjuncts fail — the concrete general-signature word the peel's four
cup/cap builders do NOT cover.  Both disjuncts fail on the concrete `2⇒2` arity. -/
theorem crossAtom_isNotCupOrCap : ¬ AtomHasCupOrCapArity crossAtom := by
  unfold AtomHasCupOrCapArity
  intro arity
  cases arity with
  | inl cupArity => exact absurd cupArity.1 (by decide)
  | inr capArity => exact absurd capArity.2 (by decide)

/-! ## Contrast: the walking adjunction is arity-locked to cup/cap -/

/-- Every walking-adjunction spine atom IS a cup or a cap (`adjunctionSpineAtom_hasCupOrCapArity`, shipped) — so
the box arm never fires at the seed and the peel's four builders are exhaustive THERE.  Re-exported to make the
ceiling's positive half explicit alongside the crossing witness. -/
theorem adjunctionAtom_hasCupOrCapArity
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode) :
    AtomHasCupOrCapArity atom :=
  adjunctionSpineAtom_hasCupOrCapArity atom

/-! ## Honesty markers -/

/-- **Honesty marker — the arc peel's ARITY CEILING is a machine-witness.**  The cup/cap event stream the peel
dispatches on is blind to a `2⇒2` crossing (`crossAtom_stepArcAtom_recordsNoCupEvent` / `_recordsNoCapEvent`,
both `rfl`), and the toy `crossModeSignature` exhibits a concrete non-cup/cap generator
(`crossAtom_isNotCupOrCap`); the walking adjunction, by contrast, is arity-locked to cup/cap
(`adjunctionAtom_hasCupOrCapArity`), so the peel's four builders `arcSwapCorePackage_{cupCup, cupCap, capCup,
capCap}` cover EXACTLY `{0⇒2, 2⇒0}` and are exhaustive only there.  `= true`. -/
def fxMode_hasArcPeelArityCeiling : Bool := true

/-- **Honesty marker — the GENERAL-signature arc peel is the open keystone (WITNESSED wall).**  The
adjunction-hardcoded dispatcher covers only `{0⇒2, 2⇒0}`; a `2⇒2` crossing (`crossAtom`) has no builder arm, and
the general-signature residual `ArcGodementSamePartitionFresh signature` remains open
(`fxMode_hasArcGodementSamePartitionFreshProof`).  The crossing witness proves the arity-lock is REAL — it does
NOT prove the general peel impossible (it is provable, just equal to grinding the keystone, out of scope for one
round).  `= false`. -/
def fxMode_hasArcPeelGeneralSignature : Bool := false

end FX1Poly.Polygraph
