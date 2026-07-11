import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # mode-3 floor — the parent Godement PARTITION residual is REFUTED AS STATED (over ∀ state)

`FreeTwoCellGodementIndependence` sharpened the `arcStructureOf` soundness residual to
`ArcGodementPartitionCommute` — the union-find PARTITION independence of transposing the two horizontally-disjoint
Godement blocks, stated as agreement of the three partition-determined EXTRACT fields (`.diagram`,
`.internalCupCounts`, `.internalCapCounts`) between the two run orders.  Its honesty marker
`fxMode_hasArcPartitionCommuteProof` there carried the STANDING NARRATIVE that the Prop is
"TRUE ... computationally confirmed ... its general zero-axiom proof is the one remaining soundness obligation."

That narrative is STALE.  The downstream sibling `FreeTwoCellArcPartitionCommute` refuted the
connectivity-level cousin `ArcGodementSamePartition` UNCONDITIONALLY (`not_arcGodementSamePartition`) — the
`∀ state` quantifier lets `state.links` name an id `≥ nextFresh`, and the two run orders then attach a boundary
node to the differently-positioned block that allocates that id first.  The SAME over-quantification afflicts the
PARENT `ArcGodementPartitionCommute`, whose FIRST conjunct is the `.diagram` equality: this file lands that
sharper refutation directly.

  ★ `not_arcGodementPartitionCommute` — `¬ ArcGodementPartitionCommute adjunctionModeSignature`, zero-axiom.
    Instantiated at the adversarial state `ArcWireState.mk [] [(100, 0)] 100 0 [] []` (a `links` edge naming
    `100 = nextFresh`), the two Godement run orders extract DIFFERENT `.diagram`s (kernel-decided on the two
    small concrete states, exactly as the sibling's `arcRefute_boundarySameComponent_differs` decides the
    connectivity divergence at boundary pair `(0, 3)`).

So the value `false` on `fxMode_hasArcPartitionCommuteProof` is CORRECT, but for a stronger reason than the
docstring claimed: as STATED (over all states) the Prop is FALSE, and it CANNOT be flipped.  The genuine,
provable residual is the FRESHNESS-conditioned `ArcGodementSamePartitionFresh`
(`fxMode_hasArcGodementSamePartitionFreshProof`), under which the disjoint-block commutation holds.  The parent's
docstring is corrected to point here (marker VALUE unchanged).

Raw Lean 4 + Init; the adversarial witness is re-exhibited from public constructors (the sibling's are private,
and the import direction is upstream), and the `.diagram` divergence is `decide` on the two small concrete
states.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The adversarial witness, re-exhibited from public constructors -/

/-- `cellAlpha` of the refuting instance: the identity 2-cell on `id_base`. -/
def refuteIdentityBase : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) := RawTwoCellExpr.id _

/-- `cellBetaUpper` of the refuting instance: the identity 2-cell on `left·right`. -/
def refuteIdentityLeftRight : RawTwoCellExpr adjunctionModeSignature
    adjunctionLeftThenRight adjunctionLeftThenRight := RawTwoCellExpr.id _

/-- The trivial base accumulator `id_base`, the whisker context for every block of the refuting instance. -/
def refuteNilBase : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- The **adversarial** starting state: a `links` edge `(100, 0)` naming id `100 = nextFresh`, which the FIRST
cup allocates as its left leg — pre-attaching that fresh leg to bottom boundary node `0`. -/
def refuteAdversarialState : ArcWireState := ArcWireState.mk [] [(100, 0)] 100 0 [] []

/-- The REDEX middle state of the refuting Godement instance: `cellAlpha`, then `cellAlphaUpper` (cup), then
`cellBeta` (cup, left-shifted context), then `cellBetaUpper`. -/
def refuteRedexState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell refuteAdversarialState refuteNilBase (composePath refuteNilBase refuteNilBase)
        refuteIdentityBase)
      refuteNilBase (composePath refuteNilBase refuteNilBase) adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase refuteIdentityLeftRight

/-- The REDUCT middle state — `cellBeta` and `cellAlphaUpper` transposed with their context shift. -/
def refuteReductState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell refuteAdversarialState refuteNilBase (composePath refuteNilBase refuteNilBase)
        refuteIdentityBase)
      (composePath refuteNilBase refuteNilBase) refuteNilBase adjunctionUnitTwoCell)
    refuteNilBase (composePath adjunctionLeftThenRight refuteNilBase) adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase refuteIdentityLeftRight

/-- The two Godement run orders extract DIFFERENT boundary `DiagramType`s — the partner matching diverges because
the adversarial `links` edge attaches bottom port `0` to the block that allocates id `100` first (the left-region
`cellAlphaUpper` in the redex, the right-region `cellBeta` in the reduct).  Kernel-decided on the two SMALL
concrete states (NOT the large parallel cells the perf rule warns against). -/
theorem refute_diagram_differs :
    (extractArc 3 refuteRedexState).diagram ≠ (extractArc 3 refuteReductState).diagram := by decide

/-- ★ **The parent Godement PARTITION residual is FALSE as stated.**  `ArcGodementPartitionCommute
adjunctionModeSignature` would force the two Godement run orders to agree on the extract `.diagram` (its first
conjunct) from EVERY starting state; instantiated at the adversarial state it forces
`(extractArc 3 redex).diagram = (extractArc 3 reduct).diagram`, contradicting `refute_diagram_differs`.  Hence the
`∀`-state residual is unprovable (refuted), sharpening the sibling's connectivity-level
`not_arcGodementSamePartition` to the parent's partition-field level.  Zero-axiom (the only nontrivial step is
`decide` on the two small concrete states). -/
theorem not_arcGodementPartitionCommute : ¬ ArcGodementPartitionCommute adjunctionModeSignature := by
  intro everyStateCommutes
  have conjuncts := everyStateCommutes refuteIdentityBase adjunctionUnitTwoCell adjunctionUnitTwoCell
    refuteIdentityLeftRight refuteNilBase refuteNilBase [] 3 refuteAdversarialState
  exact refute_diagram_differs conjuncts.1

/-! ## Honesty marker -/

/-- **Honesty marker — the parent Godement PARTITION residual is REFUTED AS STATED.**
`not_arcGodementPartitionCommute` proves `¬ ArcGodementPartitionCommute adjunctionModeSignature` zero-axiom, at
the adversarial state whose `links` names an id `≥ nextFresh` (the two run orders then extract different
`.diagram`s).  This overturns the parent marker's stale "TRUE-but-unproven" narrative: as STATED (over all
states) the residual is FALSE, so `fxMode_hasArcPartitionCommuteProof` stays `false` and CANNOT be flipped — the
genuine provable residual is the FRESHNESS-conditioned `ArcGodementSamePartitionFresh`
(`fxMode_hasArcGodementSamePartitionFreshProof`).  The parent's docstring is corrected to point here (its marker
value unchanged).  `= true`. -/
def fxMode_hasArcPartitionCommuteRefutedAsStated : Bool := true

end FX1Poly.Polygraph
