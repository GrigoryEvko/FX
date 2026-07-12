import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapCorePackage
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCrossingCountSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulSpineInvariantThreading
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # MODE-COMMUTE — the spine-level cup-cup extract corollary over the FAITHFUL engine

The adjudicated composition architecture (r18).  The shipped bare-spine peel
`extractArc_eq_rest_of_swapCorePackage` already threads a two-step swap CORE through an arbitrary
suffix `rest` and reads off equal extracts — but over the SHIPPED engine `processArcSpine`, whose
`2 -> 2` box arm is machine-witnessed CORRUPT (`ArcCrossingBoxArmCorruption`).  A suffix carrying
a genuine crossing therefore cannot be admitted there.  This file ports that peel to the FAITHFUL
engine `processArcSpineFaithful` (whose `2 -> 2` arm is the corrected `stepCrossArc`), so the
suffix may carry crossings, and instantiates it at the CUP x CUP swap — the only ALLOCATING
(up-to-renaming) generator combination.

Why the partition route.  The renaming produced by a cup-cup swap NEVER threads across the run as
a per-step extract equality — the intermediate states differ by the fresh-block transposition
`sigma` FOREVER (there is no per-step extract equality to compose, so a per-step transitivity route
fails).  What is invariant is the `sigma`-twisted PARTITION view `ArcPartitionSim`, folded through
the suffix as a single preserved invariant with ONE extract read-off at the final states.  The
partition step (`arcPartitionSim_stepArcAtom`, shipped) is FRESHNESS-FREE (only `sigmaFixesZero` +
`fixesAbove`), so — unlike the count route `ArcStepSimCount` which would additionally thread
`ArcStateFresh` / `0 < nextFresh` (propext-risky through the `Nat.sub` freshness bookkeeping) — the
faithful fold needs no per-atom freshness lemma.  This is exactly the up-to-injective-substitution
enhancement of the concurrency literature (Sangiorgi-Walker; Madiot-Pous-Sangiorgi): the
fresh-block permutation is invertible, so the step pulls back through it, so the two runs stay
`sigma`-related through every suffix step; the extract is the equivariant (singleton-orbit) read-off
(Bojanczyk-Klin-Lasota nominal orbits; Pitts-Stark (Swap) allocation-order immateriality).

## The bricks (in dependency order)

  * `arcPartitionSim_stepCrossArc` — the crossing preserves the partition simulation.  `stepCrossArc`
    touches ONLY `openWires`, so `nfEq` / `loopsEq` / `componentsCorr` / `cupCountCorr` / `capCountCorr`
    / `forestS` / `forestT` are the input `sim`'s own fields; the one new field `openMap` is
    `natListSwapTwoAt_map` in window (`position + 1 < stateS.openWires.length`).  The partition-level
    twin of the shipped count-level `arcStepSimCount_stepCrossArc`, freshness-free.
  * `arcPartitionSim_stepArcAtomFaithful` — the faithful engine's per-atom partition step: a cup or a
    cap routes to the shipped `arcPartitionSim_stepArcAtom` through the cup/cap byte-identity, a
    crossing (in window) routes to `arcPartitionSim_stepCrossArc`.
  * `SpineAdmissibleFaithful` — the per-atom running-state admissibility predicate: each atom is a
    cup / cap / crossing-in-window AT ITS RUNNING STATE (the crossing window is state-dependent, so
    it is checked against the state after the prefix).
  * `arcPartitionSim_processArcSpineFaithful` — THE SUFFIX FOLD.  Structural on the atom list, head via
    the per-atom step, tail threading the shrinking `fixesAbove` (`stepArcAtomFaithful_nextFresh_le`)
    and the running-state admissibility.
  * `stepArcAtomFaithful_cupEventNodes_length` / `_capEventNodes_length` and their folds — the
    UNCONDITIONAL event-length accounting (a faithful cup adds one cup node, a cap one cap node, a
    crossing / box none): the faithful increment equals the shipped one, so `cupAtomCount` /
    `capAtomCount` transport verbatim.  Re-establishes the two extract-count agreements at the final
    states from the cores'.
  * `extractArc_eq_rest_faithful_of_swapCorePackage` — the assembly: any `ArcSwapCorePackage`'s cores
    commute through an admissible faithful suffix at the extract (the faithful analogue of the shipped
    `extractArc_eq_rest_of_swapCorePackage`).
  * `arcFaithfulCupCupSuffixExtractCommute` — ★ THE DELIVERY: the CUP x CUP swap (its
    fresh-block-transposition renaming) commutes through an admissible crossing-carrying faithful
    suffix at the extract, built off `arcSwapCorePackage_cupCup`.

## Honest scope (the B3 cap wall)

The delivery is CUP x CUP ONLY.  Cap-involving ALLOCATING swaps are EXCLUDED: the cap MERGE flips a
merged root against the join order (`ArcCoreSwapCapFlipRefutation` / `MatchingSwapObstruction` — the
renaming vehicle provably cannot realise a cap swap at the seed).  No cap-swap corollary or instance
is shipped, and the marker `fxMode_hasArcFaithfulCupCupSuffixCommute` claims ONLY the cup-cup literal
delivery.  The permanent keystones stay `false` (`fxMode_hasArcPeelGeneralSignature`,
`fxMode_hasArcGodementSamePartitionFreshProof`, `fxMode_hasArcGodementSwapRenameableProof2` — the
#2043 / WP-AMALG mode-side interface is out of lane and untouched).  The shipped `stepArcAtom`, the
corrupt box arm, and every r1-r17 file are never edited; this certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion (fuel = the atom list), no `omega` / `simp`-AC /
`WellFounded.fix` / quotients / `propext`.  Per-declaration `#assert_no_axioms` AND an independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## K1.a — the faithful crossing preserves the partition simulation -/

/-- ★ **The faithful crossing preserves `ArcPartitionSim` (the partition-level THIRD arm).**  A
`stepCrossArc` is an adjacent transposition of the two live open wires that touches ONLY `openWires`;
so `nfEq` / `loopsEq` / `componentsCorr` / `cupCountCorr` / `capCountCorr` / `forestS` / `forestT` are
the input `sim`'s own fields verbatim (`.links`, `.nextFresh`, `.loops`, the two event lists are all
unchanged).  The one genuinely new field is `openMap`: transposing the two live wires of the target
equals `sigma`-mapping the transposed source wires, by `natListSwapTwoAt_map` in the standing window
`position + 1 < stateS.openWires.length`.  Freshness-free — the partition-level twin of the shipped
count-level `arcStepSimCount_stepCrossArc`, needing neither `sigma 0 = 0` nor injectivity for the
crossing step itself. -/
theorem arcPartitionSim_stepCrossArc (sigma : Nat → Nat)
    (stateS stateT : ArcWireState) (position : Nat)
    (window : position + 1 < stateS.openWires.length)
    (sim : ArcPartitionSim sigma stateS stateT) :
    ArcPartitionSim sigma (stepCrossArc stateS position) (stepCrossArc stateT position) where
  openMap := by
    show natListSwapTwoAt stateT.openWires position
        = (natListSwapTwoAt stateS.openWires position).map sigma
    rw [sim.openMap, natListSwapTwoAt_map sigma stateS.openWires position window]
  nfEq := sim.nfEq
  loopsEq := sim.loopsEq
  componentsCorr := sim.componentsCorr
  cupCountCorr := sim.cupCountCorr
  capCountCorr := sim.capCountCorr
  forestS := sim.forestS
  forestT := sim.forestT

/-! ## K1.b — the faithful engine's per-atom partition step -/

/-- ★ **The faithful engine's per-atom partition simulation (each arm).**  `stepArcAtomFaithful` has
three real arms: a `0 -> 2` cup and a `2 -> 0` cap fire exactly as the shipped `stepArcAtom` does, and
a `2 -> 2` crossing fires `stepCrossArc`.  On a cup or a cap the partition simulation is the shipped
`arcPartitionSim_stepArcAtom`, transported through the byte-identity
`stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`; on a crossing (in window) it is the new
`arcPartitionSim_stepCrossArc`.  The partition-level twin of the count-level `arcStepSimCountFaithful_step`,
DROPPING its freshness hypotheses (`freshS` / `freshT` / `nfPosS`) because the partition step is
freshness-free.  The corrupt box fallback is out of scope — the admissibility predicate excludes it. -/
theorem arcPartitionSim_stepArcAtomFaithful {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (isCupCapOrCross : AtomHasCupOrCapArity atom
      ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 2
          ∧ atom.leftContext.length + 1 < stateS.openWires.length))
    (sim : ArcPartitionSim sigma stateS stateT) :
    ArcPartitionSim sigma (stepArcAtomFaithful stateS atom) (stepArcAtomFaithful stateT atom) := by
  cases isCupCapOrCross with
  | inl cupOrCap =>
      rw [stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap stateS atom cupOrCap,
        stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap stateT atom cupOrCap]
      exact arcPartitionSim_stepArcAtom sigma sigmaFixesZero stateS stateT atom fixesAbove sim
  | inr crossData =>
      obtain ⟨domTwo, codTwo, window⟩ := crossData
      rw [stepArcAtomFaithful_eq_stepCrossArc_of_crossArity stateS atom domTwo codTwo,
        stepArcAtomFaithful_eq_stepCrossArc_of_crossArity stateT atom domTwo codTwo]
      exact arcPartitionSim_stepCrossArc sigma stateS stateT atom.leftContext.length window sim

/-! ## The running-state admissibility predicate -/

/-- The per-atom faithful-suffix admissibility, checked at each atom's RUNNING state: every atom is a
cup / cap or a crossing whose window fits the state reached after its prefix.  Structural on the atom
list (the state threads through `stepArcAtomFaithful`); a full `nil` / `cons` enumeration, propext-free.
An all-cup/cap suffix satisfies this trivially — but that collapses to the shipped engine
(`processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap`); the crossing-carrying case is the point. -/
def SpineAdmissibleFaithful {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → ArcWireState → Prop
  | [], _ => True
  | atom :: rest, state =>
      (AtomHasCupOrCapArity atom
        ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 2
            ∧ atom.leftContext.length + 1 < state.openWires.length))
      ∧ SpineAdmissibleFaithful rest (stepArcAtomFaithful state atom)

/-! ## K1.c — THE SUFFIX FOLD -/

/-- ★ **The partition simulation folds over a faithful spine.**  Structural recursion on the atom list:
the head is one `arcPartitionSim_stepArcAtomFaithful` step (its per-atom admissibility read from the
running-state predicate, its window at the running redex state), the tail threads the shrinking
`fixesAbove` (`stepArcAtomFaithful_nextFresh_le`) and the residual admissibility.  Freshness-free — the
faithful twin of the shipped `arcPartitionSim_processArcSpine`, admitting crossings in the suffix. -/
theorem arcPartitionSim_processArcSpineFaithful {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateS stateT : ArcWireState) →
    (∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) →
    SpineAdmissibleFaithful atoms stateS →
    ArcPartitionSim sigma stateS stateT →
    ArcPartitionSim sigma (processArcSpineFaithful stateS atoms) (processArcSpineFaithful stateT atoms)
  | [], _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, fixesAbove, admissible, sim => by
      have admissibleExpanded :
          (AtomHasCupOrCapArity atom
            ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 2
                ∧ atom.leftContext.length + 1 < stateS.openWires.length))
          ∧ SpineAdmissibleFaithful rest (stepArcAtomFaithful stateS atom) := admissible
      show ArcPartitionSim sigma (processArcSpineFaithful (stepArcAtomFaithful stateS atom) rest)
        (processArcSpineFaithful (stepArcAtomFaithful stateT atom) rest)
      exact arcPartitionSim_processArcSpineFaithful sigma sigmaFixesZero rest
        (stepArcAtomFaithful stateS atom) (stepArcAtomFaithful stateT atom)
        (fun identifier idAtLeast =>
          fixesAbove identifier
            (Nat.le_trans (stepArcAtomFaithful_nextFresh_le stateS atom) idAtLeast))
        admissibleExpanded.2
        (arcPartitionSim_stepArcAtomFaithful sigma sigmaFixesZero stateS stateT atom fixesAbove
          admissibleExpanded.1 sim)

/-! ## K1.d — the faithful event-length accounting (unconditional) -/

/-- One faithful step changes the cup-event-node count by exactly one (a `0 -> 2` cup) or zero (a cap,
a crossing, or the box) — the SAME increment as the shipped `stepArcAtom_cupEventNodes_length`, since the
crossing and box arms leave `cupEventNodes` untouched.  By cases on the arity match mirroring
`stepArcAtomFaithful` (the extra `2 -> 2` crossing sub-case at `domLen = 2` also leaves `cupEventNodes`
untouched); each leaf is `rfl`. -/
theorem stepArcAtomFaithful_cupEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepArcAtomFaithful state atom).cupEventNodes.length
      = state.cupEventNodes.length
        + (if atom.generatorDom.length == 0 && atom.generatorCod.length == 2 then 1 else 0) := by
  unfold stepArcAtomFaithful
  generalize atom.generatorDom.length = domLen
  generalize atom.generatorCod.length = codLen
  cases domLen with
  | zero =>
    cases codLen with
    | zero => rfl
    | succ codLenPred =>
      cases codLenPred with
      | zero => rfl
      | succ codLenPredPred =>
        cases codLenPredPred with
        | zero => rfl
        | succ _ => rfl
  | succ domLenPred =>
    cases domLenPred with
    | zero => rfl
    | succ domLenPredPred =>
      cases domLenPredPred with
      | zero =>
        cases codLen with
        | zero => rfl
        | succ codLenPred =>
          cases codLenPred with
          | zero => rfl
          | succ codLenPredPred =>
            cases codLenPredPred with
            | zero => rfl
            | succ _ => rfl
      | succ _ => rfl

/-- One faithful step changes the cap-event-node count by exactly one (a `2 -> 0` cap) or zero — the dual
of `stepArcAtomFaithful_cupEventNodes_length`, again the shipped increment (crossing / box leave
`capEventNodes` untouched). -/
theorem stepArcAtomFaithful_capEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepArcAtomFaithful state atom).capEventNodes.length
      = state.capEventNodes.length
        + (if atom.generatorDom.length == 2 && atom.generatorCod.length == 0 then 1 else 0) := by
  unfold stepArcAtomFaithful
  generalize atom.generatorDom.length = domLen
  generalize atom.generatorCod.length = codLen
  cases domLen with
  | zero =>
    cases codLen with
    | zero => rfl
    | succ codLenPred =>
      cases codLenPred with
      | zero => rfl
      | succ codLenPredPred =>
        cases codLenPredPred with
        | zero => rfl
        | succ _ => rfl
  | succ domLenPred =>
    cases domLenPred with
    | zero => rfl
    | succ domLenPredPred =>
      cases domLenPredPred with
      | zero =>
        cases codLen with
        | zero => rfl
        | succ codLenPred =>
          cases codLenPred with
          | zero => rfl
          | succ codLenPredPred =>
            cases codLenPredPred with
            | zero => rfl
            | succ _ => rfl
      | succ _ => rfl

/-- The faithful fold accumulates exactly `cupAtomCount` cup-event nodes onto the starting state — by
structural recursion on the atom list, the head via `stepArcAtomFaithful_cupEventNodes_length`.  Since the
faithful per-step increment equals the shipped one, the engine-independent `cupAtomCount` transports. -/
theorem processArcSpineFaithful_cupEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (processArcSpineFaithful state atoms).cupEventNodes.length
      = state.cupEventNodes.length + cupAtomCount atoms
  | [], _ => rfl
  | atom :: rest, state => by
      show (processArcSpineFaithful (stepArcAtomFaithful state atom) rest).cupEventNodes.length = _
      rw [processArcSpineFaithful_cupEventNodes_length rest (stepArcAtomFaithful state atom),
        stepArcAtomFaithful_cupEventNodes_length state atom]
      dsimp only [cupAtomCount]
      rw [Nat.add_assoc]

/-- The faithful fold accumulates exactly `capAtomCount` cap-event nodes onto the starting state — the dual
of `processArcSpineFaithful_cupEventNodes_length`. -/
theorem processArcSpineFaithful_capEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (processArcSpineFaithful state atoms).capEventNodes.length
      = state.capEventNodes.length + capAtomCount atoms
  | [], _ => rfl
  | atom :: rest, state => by
      show (processArcSpineFaithful (stepArcAtomFaithful state atom) rest).capEventNodes.length = _
      rw [processArcSpineFaithful_capEventNodes_length rest (stepArcAtomFaithful state atom),
        stepArcAtomFaithful_capEventNodes_length state atom]
      dsimp only [capAtomCount]
      rw [Nat.add_assoc]

/-! ## K1.e — the assembly + the CUP x CUP delivery -/

/-- ★ **The FAITHFUL bare-spine peel.**  Any swap-core package yields equal FAITHFUL-run extracts after a
common admissible `rest` continuation — the faithful analogue of the shipped
`extractArc_eq_rest_of_swapCorePackage`, over `processArcSpineFaithful` (so `rest` may carry crossings, an
option the shipped engine's corrupt box arm forbids).  The core partition simulation folds through the
suffix (`arcPartitionSim_processArcSpineFaithful`), and the two extract-count agreements are re-established
at the final states from the cores' via the faithful event-length accounting. -/
theorem extractArc_eq_rest_faithful_of_swapCorePackage {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (redexCore reductCore : ArcWireState)
    (package : ArcSwapCorePackage bottomCount redexCore reductCore)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (admissible : SpineAdmissibleFaithful rest redexCore) :
    extractArc bottomCount (processArcSpineFaithful redexCore rest)
      = extractArc bottomCount (processArcSpineFaithful reductCore rest) := by
  have restSim : ArcPartitionSim package.sigma (processArcSpineFaithful redexCore rest)
      (processArcSpineFaithful reductCore rest) :=
    arcPartitionSim_processArcSpineFaithful package.sigma package.sigmaFixesZero rest
      redexCore reductCore package.fixesAbove admissible package.coreSim
  have cupPin : (processArcSpineFaithful redexCore rest).cupEventNodes.length
      = (processArcSpineFaithful reductCore rest).cupEventNodes.length := by
    rw [processArcSpineFaithful_cupEventNodes_length rest redexCore,
      processArcSpineFaithful_cupEventNodes_length rest reductCore, package.cupLengthsAgree]
  have capPin : (processArcSpineFaithful redexCore rest).capEventNodes.length
      = (processArcSpineFaithful reductCore rest).capEventNodes.length := by
    rw [processArcSpineFaithful_capEventNodes_length rest redexCore,
      processArcSpineFaithful_capEventNodes_length rest reductCore, package.capLengthsAgree]
  exact extractArc_eq_of_arcPartitionSim bottomCount package.sigma package.sigmaFixesZero
    package.fixesBoundary (processArcSpineFaithful redexCore rest)
    (processArcSpineFaithful reductCore rest) restSim cupPin capPin

/-- ★ **THE CUP x CUP FAITHFUL SUFFIX DELIVERY.**  The two run orders of a CUP x CUP swap
(`stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow)` low-first vs
`stepCupArc (stepCupArc state (gap + positionLow)) positionLow` high-first), which differ by the
fresh-block transposition `arcFreshBlockTransposition state.nextFresh 3 3`, extract to EQUAL
`FullArcStructure`s after ANY admissible (crossing-carrying) faithful suffix `rest`.  Built off
`arcSwapCorePackage_cupCup` fed to the faithful bare-spine peel.  This is the r18 keystone: the
extraction-invariant cup-cup commutation over the FAITHFUL engine, honestly scoped away from
cap-swap pairs (the B3 cap wall). -/
theorem arcFaithfulCupCupSuffixExtractCommute {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat) (positionBound : gap + positionLow ≤ state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (admissible : SpineAdmissibleFaithful rest
      (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow))) :
    extractArc bottomCount
        (processArcSpineFaithful
          (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow)) rest)
      = extractArc bottomCount
          (processArcSpineFaithful
            (stepCupArc (stepCupArc state (gap + positionLow)) positionLow) rest) :=
  extractArc_eq_rest_faithful_of_swapCorePackage bottomCount _ _
    (arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount boundaryBelowFresh
      gap positionLow positionBound)
    rest admissible

/-! ## Non-vacuity — the delivery FIRES on a suffixed spine with a refl-failure probe -/

/-- A width-6 fresh forest seed: open wires `[0..5]`, empty links, `nextFresh = 6`. -/
def cupCupSuffixProbeSeed : ArcWireState := ArcWireState.mk (List.range 6) [] 6 0 [] []

/-- ★ **Non-vacuous: the cup-cup faithful suffix delivery fires on a REAL crossing-carrying suffix.**  On
the width-6 fresh seed, the CUP x CUP swap at `gap = 2`, `positionLow = 0` (window `2 <= 6`) followed by
the concrete `2 -> 2` crossing `crossAtom` (admissible: its window `1 < 10` fits the width-10 two-cup core)
extracts EQUALLY on the low-first and high-first orders.  A genuine instantiation of
`arcFaithfulCupCupSuffixExtractCommute` over a suffix that the SHIPPED engine's corrupt box arm could not
carry, not a hand fixture. -/
theorem arcFaithfulCupCupSuffixCommute_nonvacuous :
    extractArc 6
        (processArcSpineFaithful
          (stepCupArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom])
      = extractArc 6
          (processArcSpineFaithful
            (stepCupArc (stepCupArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]) :=
  arcFaithfulCupCupSuffixExtractCommute cupCupSuffixProbeSeed (arcStateFresh_initial 6)
    isUnionFindForest_nil (by decide) 6 (by decide) 2 0 (by decide) [crossAtom]
    ⟨Or.inr ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length, by decide⟩, trivial⟩

/-- ★ **Refl-failure probe: the two run states GENUINELY DIFFER.**  The low-first and high-first cup-cup
runs (after the shared crossing suffix) have DIFFERENT open-wire lists — the fresh-block transposition is a
real, non-identity renaming.  So `arcFaithfulCupCupSuffixCommute_nonvacuous` is content-bearing: the extract
equality is NOT `rfl` on the states, it is the partition-fold invariance absorbing an actual renaming.  By
`decide` on the concrete open-wire lists. -/
theorem arcFaithfulCupCupSuffixCommute_statesDiffer :
    (processArcSpineFaithful
        (stepCupArc (stepCupArc cupCupSuffixProbeSeed 0) (2 + 2 + 0)) [crossAtom]).openWires
      ≠ (processArcSpineFaithful
          (stepCupArc (stepCupArc cupCupSuffixProbeSeed (2 + 0)) 0) [crossAtom]).openWires := by
  decide

/-! ## Honesty marker + permanent-false pins -/

/-- **Honesty marker — the CUP x CUP faithful suffix extract commutation is SHIPPED.**  The two run orders
of a cup-cup swap, differing by the fresh-block transposition, extract EQUALLY after ANY admissible
crossing-carrying faithful suffix (`arcFaithfulCupCupSuffixExtractCommute`), built by folding the core
`ArcPartitionSim` through the suffix (`arcPartitionSim_processArcSpineFaithful`, over the corrected
`stepCrossArc` arm `arcPartitionSim_stepCrossArc` / `arcPartitionSim_stepArcAtomFaithful`) and reading off a
single extract at the final states with the event-count agreements re-established unconditionally
(`processArcSpineFaithful_cupEventNodes_length` / `_capEventNodes_length`).  Non-vacuous on a real
crossing-carrying suffix with the two states genuinely renamed
(`arcFaithfulCupCupSuffixCommute_nonvacuous` / `_statesDiffer`).  HONEST SCOPE: cup-cup ONLY — cap-swap
pairs are excluded (the B3 cap wall: cap merges flip roots).  Nothing shipped is edited.  `= true`. -/
def fxMode_hasArcFaithfulCupCupSuffixCommute : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The faithful cup-cup suffix
peel does not build the crossing-inclusive general block-swap witness over arbitrary faithful cells;
`fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcFaithfulCupCupSuffixCommute_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**  The mode-side
general-signature peel `ArcGodementSamePartitionFresh` lives out of lane; this file does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcFaithfulCupCupSuffixCommute_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the count-route block-swap witness stays the shared wall.**  The crossing-inclusive
general faithful block-swap `sigma` over arbitrary cells is the same open Mazurkiewicz residual (2) the
count route names; `fxMode_hasArcGodementSwapRenameableProof2` stays `false`.  `rfl`. -/
theorem arcFaithfulCupCupSuffixCommute_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
