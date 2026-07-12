import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapMapEquivariance
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshSelfSimulation

/-! # MODE-COMMUTE — the faithful crossing arm as a count-simulation step (the third arm over `stepArcAtomFaithful`)

The count-route `ArcStepSimCount` (in `ArcSwapRenameable`) is the LIVE, order-insensitive per-atom simulation
invariant: two arc states are related by a node renaming `sigma : Nat -> Nat` when the open wires are a pointwise
`sigma`-image, `sigma` is a union-find automorphism (`rootComm`), the loop counts agree, and the per-root cup/cap
event COUNTS correspond (`cupCorr` / `capCorr`), with both link lists forests.  The shipped step-stability lemma
`arcStepSimCount_step` proves the invariant survives one `stepArcAtom` step — but `stepArcAtom` is CUP/CAP-LOCKED:
its `2 -> 2` box arm is machine-witnessed CORRUPT (`ArcCrossingBoxArmCorruption`), never reached at the
walking-adjunction seed.

`stepArcAtomFaithful` (in `ArcCrossingFaithfulStep`) is the additive-sibling engine with the CORRECTED `2 -> 2`
arm: a faithful symmetric crossing `stepCrossArc` — an adjacent transposition of the two live open wires that
PRESERVES width, leaves the union-find forest and `nextFresh` UNTOUCHED, and records no arc event.  This file
supplies the count-simulation's THIRD arm:

  * S2 — `arcStepSimCount_stepCrossArc`: the crossing preserves `ArcStepSimCount`.  The genuinely new content is
    `openMap`, discharged by `natListSwapTwoAt_map` (the renaming-equivariance of the adjacent transposition, in
    window `position + 1 < stateS.openWires.length`); every other field passes through UNCHANGED because
    `stepCrossArc` touches only `openWires` (`rootComm` / `cupCorr` / `capCorr` / `loopsEq` / `nfEq` / forests are
    the input `sim`'s own fields).  `arcStepSimCountFaithful_step` then dispatches the faithful engine's three real
    arms: a cup or a cap routes to the shipped `arcStepSimCount_step` through the byte-identity
    `stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`, and a crossing routes to the new lemma.

  * S3 — `extractArc_eq_of_arcStepSimCount` reads a count-simulation off into an EQUAL faithful extract (via the
    shipped `arcRenameRel_of_arcStepSimCount` -> `sameArcPartition_of_renameRel` -> `extractArc_eq_of_sameArcPartition`
    chain); `extractArc_stepCrossArc_eq_of_arcStepSimCount` is the two-order consequence at a crossing:
    `sigma`-related states cross to states with equal extracts.  `sameArcPartition_stepCrossArc_of_arcStepSimCount`
    exposes the intermediate partition-view witness the freshness-conditioned keystone consumes.  Non-vacuity is a
    concrete crossing instance built from the shipped fresh-block self-simulation.

  * S4 — the keystone adjudication.  The faithful analogue of the general-signature partition keystone
    `ArcGodementSamePartitionFresh` — the crossing-inclusive block-swap `sigma` over ARBITRARY faithful cells — is
    the SAME open Mazurkiewicz-independence wall the count route already names (`ArcGodementCoreSwapSimCount`,
    residual (2), `fxMode_hasArcGodementSwapRenameableProof2 = false`).  This file supplies the crossing STEP for
    that construction, not the construction; the permanent keystones stay `false`
    (`fxMode_hasArcGodementSamePartitionFreshProof`, `fxMode_hasArcPeelGeneralSignature`, re-asserted by `rfl`).

Nothing shipped is edited: `stepArcAtom`, `stepArcAtomFaithful`, `stepCrossArc`, `ArcStepSimCount` and the parent
residuals are untouched; this certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `WellFounded.fix` / quotients.  Per-declaration
`#assert_no_axioms` AND an independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## S2 — the crossing arm preserves the count simulation -/

/-- The faithful crossing reduces `stepArcAtomFaithful` (its `2 -> 2` arm) — mirror of the shipped cup/cap
identity `stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`.  Given the atom's crossing arity, `stepArcAtomFaithful`
fires `stepCrossArc` at the atom's live position.  `dsimp` exposes the arity match; the two length rewrites reduce
it to the `2 -> 2` arm. -/
theorem stepArcAtomFaithful_eq_stepCrossArc_of_crossArity {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (domTwo : atom.generatorDom.length = 2) (codTwo : atom.generatorCod.length = 2) :
    stepArcAtomFaithful state atom = stepCrossArc state atom.leftContext.length := by
  dsimp only [stepArcAtomFaithful]
  rw [domTwo, codTwo]

/-- ★ **The faithful crossing preserves the count simulation (the THIRD arm).**  `stepCrossArc` is an adjacent
transposition of the two live open wires that touches ONLY `openWires`; so `nfEq` / `rootComm` / `loopsEq` /
`cupCorr` / `capCorr` / `forestS` / `forestT` are the input `sim`'s own fields verbatim (the links, `nextFresh`,
loop count and event lists are all unchanged).  The one genuinely new field is `openMap`: transposing the two live
wires of the target equals `sigma`-mapping the transposed source wires, by `natListSwapTwoAt_map` (the renaming
equivariance of the adjacent transposition) in the standing window `position + 1 < stateS.openWires.length`.  No
`sigma 0 = 0` and no injectivity is needed for the crossing step itself — the swap-map brick renames the two
spliced reads with no side condition. -/
theorem arcStepSimCount_stepCrossArc (sigma : Nat → Nat)
    (stateS stateT : ArcWireState) (position : Nat)
    (window : position + 1 < stateS.openWires.length)
    (sim : ArcStepSimCount sigma stateS stateT) :
    ArcStepSimCount sigma (stepCrossArc stateS position) (stepCrossArc stateT position) where
  openMap := by
    show natListSwapTwoAt stateT.openWires position
        = (natListSwapTwoAt stateS.openWires position).map sigma
    rw [sim.openMap, natListSwapTwoAt_map sigma stateS.openWires position window]
  nfEq := sim.nfEq
  rootComm := sim.rootComm
  loopsEq := sim.loopsEq
  cupCorr := sim.cupCorr
  capCorr := sim.capCorr
  forestS := sim.forestS
  forestT := sim.forestT

/-- ★ **The faithful engine's per-atom count simulation (each arm).**  `stepArcAtomFaithful` has three real arms:
a `0 -> 2` cup and a `2 -> 0` cap fire exactly as the shipped `stepArcAtom` does, and a `2 -> 2` crossing fires
`stepCrossArc`.  On a cup or a cap the count simulation is the shipped `arcStepSimCount_step`, transported through
the byte-identity `stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`; on a crossing (in window) it is the new
`arcStepSimCount_stepCrossArc`.  The corrupt box fallback is out of scope — it never fires at the
walking-adjunction seed and carries no arc semantics. -/
theorem arcStepSimCountFaithful_step {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (freshS : ArcStateFresh stateS) (freshT : ArcStateFresh stateT) (nfPosS : 0 < stateS.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (isCupCapOrCross : AtomHasCupOrCapArity atom
      ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 2
          ∧ atom.leftContext.length + 1 < stateS.openWires.length))
    (sim : ArcStepSimCount sigma stateS stateT) :
    ArcStepSimCount sigma (stepArcAtomFaithful stateS atom) (stepArcAtomFaithful stateT atom) := by
  cases isCupCapOrCross with
  | inl cupOrCap =>
      rw [stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap stateS atom cupOrCap,
        stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap stateT atom cupOrCap]
      exact arcStepSimCount_step sigma inj sigmaFixesZero stateS stateT atom freshS freshT nfPosS fixesAbove sim
  | inr crossData =>
      obtain ⟨domTwo, codTwo, window⟩ := crossData
      rw [stepArcAtomFaithful_eq_stepCrossArc_of_crossArity stateS atom domTwo codTwo,
        stepArcAtomFaithful_eq_stepCrossArc_of_crossArity stateT atom domTwo codTwo]
      exact arcStepSimCount_stepCrossArc sigma stateS stateT atom.leftContext.length window sim

/-! ## S3 — the extract consequence (a count simulation reads off into an equal faithful extract) -/

/-- ★ **A count simulation yields an EQUAL extract.**  `arcRenameRel_of_arcStepSimCount` reads the invariant off as
`ArcRenameRel`, `sameArcPartition_of_renameRel` turns that into `SameArcPartition` (the renaming-invariance of the
partition view), and `extractArc_eq_of_sameArcPartition` closes to extract equality once the two total cup/cap
event counts agree.  The fresh wire-ids the two run orders allocate differently are exactly the renaming's content
— invisible to the extract. -/
theorem extractArc_eq_of_arcStepSimCount (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState)
    (cupCountAgree : stateS.cupEventNodes.length = stateT.cupEventNodes.length)
    (capCountAgree : stateS.capEventNodes.length = stateT.capEventNodes.length)
    (sim : ArcStepSimCount sigma stateS stateT) :
    extractArc bottomCount stateS = extractArc bottomCount stateT :=
  extractArc_eq_of_sameArcPartition bottomCount stateS stateT
    (sameArcPartition_of_renameRel bottomCount sigma stateS stateT
      (arcRenameRel_of_arcStepSimCount bottomCount sigma inj sigmaFixesZero fixesBoundary stateS stateT sim))
    cupCountAgree capCountAgree

/-- ★ **The two-order partition witness at a crossing.**  Two `sigma`-related states, crossed at the same position,
are `SameArcPartition` — exactly the freshness-conditioned partition witness the keystone
`ArcGodementSamePartitionFresh` consumes, now over the faithful crossing arm.  (`stepCrossArc` preserves the total
cup/cap event lists, so the extract's cup/cap counts also agree — see the extract corollary below.) -/
theorem sameArcPartition_stepCrossArc_of_arcStepSimCount (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState) (position : Nat)
    (window : position + 1 < stateS.openWires.length)
    (sim : ArcStepSimCount sigma stateS stateT) :
    SameArcPartition bottomCount (stepCrossArc stateS position) (stepCrossArc stateT position) :=
  sameArcPartition_of_renameRel bottomCount sigma
    (stepCrossArc stateS position) (stepCrossArc stateT position)
    (arcRenameRel_of_arcStepSimCount bottomCount sigma inj sigmaFixesZero fixesBoundary
      (stepCrossArc stateS position) (stepCrossArc stateT position)
      (arcStepSimCount_stepCrossArc sigma stateS stateT position window sim))

/-- ★ **The crossing commutes with the extract up to the renaming.**  Two `sigma`-related states, crossed at the
same position, extract to EQUAL `FullArcStructure`s.  The crossing preserves the total cup/cap event lists, so the
source states' count agreements transport verbatim.  This is the faithful crossing's two-order extract
consequence. -/
theorem extractArc_stepCrossArc_eq_of_arcStepSimCount (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState) (position : Nat)
    (window : position + 1 < stateS.openWires.length)
    (cupCountAgree : stateS.cupEventNodes.length = stateT.cupEventNodes.length)
    (capCountAgree : stateS.capEventNodes.length = stateT.capEventNodes.length)
    (sim : ArcStepSimCount sigma stateS stateT) :
    extractArc bottomCount (stepCrossArc stateS position)
      = extractArc bottomCount (stepCrossArc stateT position) :=
  extractArc_eq_of_arcStepSimCount bottomCount sigma inj sigmaFixesZero fixesBoundary
    (stepCrossArc stateS position) (stepCrossArc stateT position)
    cupCountAgree capCountAgree
    (arcStepSimCount_stepCrossArc sigma stateS stateT position window sim)

/-! ## Non-vacuity — a concrete crossing preserves a NON-identity count simulation -/

/-- A width-4 fresh forest seed: open wires `[0,1,2,3]`, empty links, `nextFresh = 4`. -/
def crossingCountSimProbeState : ArcWireState := ArcWireState.mk (List.range 4) [] 4 0 [] []

/-- ★ **Non-vacuous: the crossing arm fires on a real, non-identity count simulation.**  The shipped fresh-block
transposition `arcFreshBlockTransposition 4 1 1` (a non-identity renaming fixing everything below `nextFresh = 4`)
relates the fresh probe state to itself (`arcStepSimCount_self_transposition`); crossing the front pair at position
`1` (window `2 < 4`) carries that count simulation through `stepCrossArc` on both sides.  A genuine instantiation
of `arcStepSimCount_stepCrossArc`, not a hand fixture. -/
theorem arcFaithfulCrossingCountSim_nonvacuous :
    ArcStepSimCount (arcFreshBlockTransposition crossingCountSimProbeState.nextFresh 1 1)
      (stepCrossArc crossingCountSimProbeState 1) (stepCrossArc crossingCountSimProbeState 1) :=
  arcStepSimCount_stepCrossArc _ crossingCountSimProbeState crossingCountSimProbeState 1
    (by decide)
    (arcStepSimCount_self_transposition 1 1 crossingCountSimProbeState
      (arcStateFresh_initial 4) isUnionFindForest_nil)

/-! ## S4 — the keystone adjudication + honesty markers

The faithful analogue of the general-signature partition keystone `ArcGodementSamePartitionFresh` — the
crossing-inclusive block-swap renaming `sigma` between the two Godement run orders over ARBITRARY faithful cells —
reduces (via `sameArcPartition_stepCrossArc_of_arcStepSimCount` folded over a spine, exactly as the shipped
`arcGodementSamePartitionFresh_of_swapRenameable` reduces the cup/cap residual) to the EXISTENCE of that block-swap
`sigma`.  That existence is the SAME open Mazurkiewicz-independence wall the count route already names:
`ArcGodementCoreSwapSimCount` / `fxMode_hasArcGodementSwapRenameableProof2 = false` (residual (2) — the geometric
support/locality analysis of the two horizontally-disjoint blocks over the fresh window).  This file supplies the
crossing STEP that construction consumes (the third arm), not the construction; the permanent keystones stay
`false`. -/

/-- **Honesty marker — the faithful crossing count-simulation arm is SHIPPED.**  `arcStepSimCount_stepCrossArc`
proves the corrected `2 -> 2` crossing (`stepCrossArc`) preserves the LIVE count-simulation invariant
`ArcStepSimCount` in window (`openMap` via `natListSwapTwoAt_map`, every other field the input `sim`'s own — the
crossing touches only `openWires`); `arcStepSimCountFaithful_step` assembles the faithful engine's three arms (cup
and cap via the shipped `arcStepSimCount_step` through the cup/cap byte-identity, crossing via the new lemma).  The
count simulation reads off into an EQUAL faithful extract (`extractArc_eq_of_arcStepSimCount`), and two
`sigma`-related states cross to states with equal extracts (`extractArc_stepCrossArc_eq_of_arcStepSimCount`) and to
a `SameArcPartition` witness (`sameArcPartition_stepCrossArc_of_arcStepSimCount`).  Non-vacuous on a real
non-identity crossing (`arcFaithfulCrossingCountSim_nonvacuous`).  Nothing shipped is edited.  `= true`. -/
def fxMode_hasArcFaithfulCrossingCountSim : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  Supplying the crossing count-simulation
step does not build the crossing-inclusive general block-swap witness; `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcFaithfulCrossingCountSim_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the fresh-partition keystone is untouched.**  The faithful analogue of
`ArcGodementSamePartitionFresh` reduces to the SAME open block-swap wall; this file does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcFaithfulCrossingCountSim_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the count-route block-swap witness stays the shared wall.**  The crossing-inclusive faithful
block-swap `sigma` over arbitrary cells is the same open Mazurkiewicz residual (2) the count route names;
`fxMode_hasArcGodementSwapRenameableProof2` stays `false`.  `rfl`. -/
theorem arcFaithfulCrossingCountSim_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
