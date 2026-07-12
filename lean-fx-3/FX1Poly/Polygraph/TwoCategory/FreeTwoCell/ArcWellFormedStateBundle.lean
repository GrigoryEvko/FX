import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointWhiskerSupport
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementFreshForestGapRefutation

/-! # MODE-COMMUTE r24 — the `WellFormedArcState` bundle, its preservation, and the joint simulation

## The adjudication (honest, probe-forced — the round shape overturned)

The r23 residual (1) — "the JOINT-STATE simulation across the two run orders, tracking `openWires` and
`nextFresh` along `sigma`" — was named as the likely r24 core.  Probing overturns that: the joint
`openWires`/`nextFresh` transport is ALREADY shipped, at per-step granularity
(`stepArcAtom_openWires_map` / `stepArcAtom_nextFresh_eq`) and at fold granularity
(`arcStepSimCount_processArcSpine`, which threads BOTH the open-wire `sigma`-image AND the fresh
counter through a whole spine).  What genuinely remains open is residual (2): the base
`ArcStepSimCount` between the two swapped-order Godement cores — `ArcGodementCoreSwapSimCount`
(`fxMode_hasArcGodementSwapRenameableProof2 = false`) — the horizontal-disjointness geometric fitting,
which is out of round.

So r24's honest, additive deliverable is a REFACTOR-BY-ADDITION following the verified-union-find
literature (Chargueraud & Pottier, JAR 2019: fold the ranked-forest acyclicity `is_rdsf` + the
representative agreement into ONE carrier `UF`, state every operation as `preserves UF`).  Here the
carrier is `WellFormedArcState` — the three per-state hypotheses that every reachable-fold lemma
already threads separately (`ArcStateFresh`, `isUnionFindForest`, `0 < nextFresh`) collapsed into ONE
predicate.  Then:

  ★ the arc-step operators each PRESERVE the bundle (`wellFormedArcState_stepCupArc` / `_stepCapArc` /
    `_stepArcAtom` / `_processArcSpine` / `_runArcCell`), pure 3-field re-assembly of shipped,
    already-axiom-audited preservation lemmas;
  ★ the r21 cyclic-forest-gap state — the machine-refuted garbage on which `ArcGodementSamePartition`
    was silently assumed — is EXCLUDED from the bundle BY CONSTRUCTION (`not_wellFormedArcState`), via
    the `isForest` field, NOT by a per-lemma hypothesis; this is the r21 lesson operationalised;
  ★ the fold-level joint simulation is RE-STATED over the bundle
    (`arcStepSimCount_processArcSpine_ofWellFormed` / `_runArcCell_ofWellFormed`), genuinely CONSUMING
    the shipped r19-era fold levers — the `(freshSource, freshTarget, nonDegenerateSource)` triple is
    read off the two bundles ONCE;
  ★ the compound-sigma JOINT per-step lever (`stepCupArc_renameState_compoundTransposition` /
    `stepCapArc_renameState_compoundTransposition`) ties residual (1) (the `openWires`/`nextFresh`
    transport via the whole-state `renameState` levers), residual (3) (the width seam
    `baseFresh + widthA + widthB <= nextFresh` discharging `fixesAbove`), and residual (4) (the
    `0 < baseFresh` corner discharging `sigmaFixesZero`) into ONE reusable adapter, genuinely consuming
    the shipped r22 `compoundFreshBlockTransposition` injectivity / fix laws.

## What stays walled (honest residual re-record)

`fxMode_hasDisjointWhiskerSupport` (the FROZEN r23 file) stays `false`.  r24 flips NO whole-cell gate.
The SOLE remaining obligation for the whisker-support list-equality is the base `ArcStepSimCount` at
the two Godement cores, `ArcGodementCoreSwapSimCount` (`fxMode_hasArcGodementSwapRenameableProof2 =
false`) — the horizontal-disjointness geometric fitting (residual (2)), inseparable from the same
partition-independence `GodementIndependence` leaves at `fxMode_hasArcPartitionCommuteProof = false`.
The bundle + levers do NOT touch it.  The FLIP LAW is respected: no partial-delivery flip.

## WRONG-TARGET flag (do not sink a future rung into this)

The order-SENSITIVE link-list equality `reduct.links = renameLinks sigma redex.links` is the shape the
corpus already corrected AWAY from: the two run orders prepend edges in swapped order, so the lists are
permutations, NOT equal.  The LIVE order-INSENSITIVE target is `ArcStepSimCount` (rootComm + count
fields), whose infrastructure is what the bundle re-exposes.  Never re-litigate the machine-refuted
`ArcGodementSamePartitionFresh` (`ArcPartitionCommute.lean:472`) — the bundle's `isForest` field
EXCLUDES its cyclic counterexample rather than re-proving it.

Raw Lean 4 + Init; every preservation proof is pure term-mode field-assembly of shipped lemmas, every
control a shipped-lemma composition or a structural `decide`, every fire the shipped lever at a
concrete instance.  Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bundle — one carrier for the three reachable-fold invariants -/

/-- ★ **The well-formed arc-state bundle.**  The three per-state hypotheses that every reachable-fold
lemma threads separately, folded into ONE predicate (the Chargueraud-Pottier `UF`-carrier move):
`ArcStateFresh` (every mentioned id `< nextFresh`), `isUnionFindForest` (acyclic link forest), and
`0 < nextFresh` (non-degenerate fresh frontier — the cap-step's past-the-end read discipline).  Reuses
the EXACT shipped predicates; adds no new recursion. -/
structure WellFormedArcState (state : ArcWireState) : Prop where
  /-- Every open wire / link endpoint / event node is below the fresh frontier. -/
  isFresh : ArcStateFresh state
  /-- The link list is an acyclic union-find forest. -/
  isForest : isUnionFindForest state.links
  /-- The fresh frontier is positive (non-degenerate empty-boundary corner excluded). -/
  isNonDegenerate : 0 < state.nextFresh

/-! ## Preservation — every arc-step operator preserves the bundle -/

/-- A CUP step preserves the bundle: freshness by `arcStateFresh_stepCupArc`, the forest by
`isUnionFindForest_stepCupArc`, and `nextFresh = old + 3 > 0` by monotone add. -/
theorem wellFormedArcState_stepCupArc (state : ArcWireState) (position : Nat)
    (wellFormed : WellFormedArcState state) : WellFormedArcState (stepCupArc state position) :=
  ⟨arcStateFresh_stepCupArc state position wellFormed.isFresh,
   isUnionFindForest_stepCupArc state position wellFormed.isForest,
   Nat.lt_of_lt_of_le wellFormed.isNonDegenerate (Nat.le_add_right _ _)⟩

/-- A CAP step preserves the bundle: freshness by `arcStateFresh_stepCapArc`, the forest by
`isUnionFindForest_stepCapArc`, and `nextFresh = old + 1 > 0` by monotone add. -/
theorem wellFormedArcState_stepCapArc (state : ArcWireState) (position : Nat)
    (wellFormed : WellFormedArcState state) : WellFormedArcState (stepCapArc state position) :=
  ⟨arcStateFresh_stepCapArc state position wellFormed.isFresh,
   isUnionFindForest_stepCapArc state position wellFormed.isForest,
   Nat.lt_of_lt_of_le wellFormed.isNonDegenerate (Nat.le_add_right _ _)⟩

/-- ★ **One arc step preserves the bundle** — cup / cap / box via the three shipped step-preservation
lemmas and the monotone-`nextFresh` lever `stepArcAtom_nextFresh_le`. -/
theorem wellFormedArcState_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (wellFormed : WellFormedArcState state) : WellFormedArcState (stepArcAtom state atom) :=
  ⟨arcStateFresh_stepArcAtom state atom wellFormed.isFresh,
   isUnionFindForest_stepArcAtom state atom wellFormed.isForest,
   Nat.lt_of_lt_of_le wellFormed.isNonDegenerate (stepArcAtom_nextFresh_le state atom)⟩

/-- ★ **The whole arc fold preserves the bundle** — the shipped spine folds of freshness / forest /
monotone `nextFresh`, re-assembled. -/
theorem wellFormedArcState_processArcSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atoms : List (SpineAtom signature sourceMode targetMode))
    (wellFormed : WellFormedArcState state) : WellFormedArcState (processArcSpine state atoms) :=
  ⟨arcStateFresh_processArcSpine atoms state wellFormed.isFresh,
   isUnionFindForest_processArcSpine atoms state wellFormed.isForest,
   Nat.lt_of_lt_of_le wellFormed.isNonDegenerate (processArcSpine_nextFresh_le atoms state)⟩

/-- ★ **Running one cell preserves the bundle** — so every state reachable by `runArcCell` from a
well-formed seed is itself well-formed (the closure the joint simulation runs over). -/
theorem wellFormedArcState_runArcCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (runArcCell state leftAcc rightAcc cell) :=
  ⟨runArcCell_arcStateFresh state leftAcc rightAcc cell wellFormed.isFresh,
   isUnionFindForest_runArcCell state leftAcc rightAcc cell wellFormed.isForest,
   Nat.lt_of_lt_of_le wellFormed.isNonDegenerate (runArcCell_nextFresh_le state leftAcc rightAcc cell)⟩

/-! ## The negative control — the r21 cyclic garbage is EXCLUDED by construction -/

/-- ★ **The r21 cyclic-forest-gap state is NOT well-formed** — even though it is fresh
(`arcFreshCyclicForestGapState_isFresh`) and non-degenerate (`nextFresh = 4 > 0`), its links
`[(0,1),(1,0),(2,3)]` are cyclic, so the `isForest` field is unsatisfiable
(`arcFreshCyclicForestGapState_notForest`).  The universal-over-raw-`ArcState` refutations of r21
CANNOT instantiate the bundle — the bundle EXCLUDES the garbage BY CONSTRUCTION, not by a decorative
per-lemma hypothesis.  This is the r21 design lesson operationalised. -/
theorem not_wellFormedArcState :
    ¬ WellFormedArcState arcFreshCyclicForestGapState :=
  fun wellFormed => arcFreshCyclicForestGapState_notForest wellFormed.isForest

/-! ## The positive control — a concrete below-base forest state IS well-formed -/

/-- A concrete below-base forest arc state: two open wires `[2,3]`, one acyclic link `(2,3)`, fresh
frontier `4`.  Every id lies below `4`, the single link is a forest, `4 > 0` — the positive witness
that the bundle is inhabited (and the seam-satisfied joint-fire fixture below). -/
def arcBelowBaseForestState : ArcWireState := ArcWireState.mk [2, 3] [(2, 3)] 4 0 [] []

/-- The below-base forest fixture is fresh (every mentioned id `< 4`).  `unfold` + structural `decide`
(the shipped `arcFreshCyclicForestGapState_isFresh` recipe). -/
theorem arcBelowBaseForestState_isFresh : ArcStateFresh arcBelowBaseForestState := by
  unfold ArcStateFresh arcBelowBaseForestState
  decide

/-- The below-base forest fixture's single link `(2,3)` is an acyclic forest — both endpoints are
parentless in the empty tail and `2 != 3`.  Via `isUnionFindForest_cons`, propext-free. -/
theorem arcBelowBaseForestState_isForest : isUnionFindForest arcBelowBaseForestState.links := by
  show isUnionFindForest [(2, 3)]
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- ★ **The below-base forest fixture IS well-formed** — the bundle is inhabited. -/
theorem arcBelowBaseForestState_isWellFormed : WellFormedArcState arcBelowBaseForestState :=
  ⟨arcBelowBaseForestState_isFresh, arcBelowBaseForestState_isForest, by decide⟩

/-- ★ **Preservation fired concretely — a cup step keeps the fixture well-formed.** -/
theorem arcBelowBaseForestState_cupReduct_isWellFormed :
    WellFormedArcState (stepCupArc arcBelowBaseForestState 0) :=
  wellFormedArcState_stepCupArc arcBelowBaseForestState 0 arcBelowBaseForestState_isWellFormed

/-- ★ **Preservation fired concretely — a cap step keeps the fixture well-formed.** -/
theorem arcBelowBaseForestState_capReduct_isWellFormed :
    WellFormedArcState (stepCapArc arcBelowBaseForestState 0) :=
  wellFormedArcState_stepCapArc arcBelowBaseForestState 0 arcBelowBaseForestState_isWellFormed

/-- ★ **Preservation fired concretely — running the identity cell (over `nilTipPath` at the walking
adjunction) keeps the fixture well-formed.**  Exercises `wellFormedArcState_runArcCell` on a concrete
cell / modality-path fixture. -/
theorem arcBelowBaseForestState_runNilCell_isWellFormed :
    WellFormedArcState (runArcCell arcBelowBaseForestState nilTipPath nilTipPath identityCellOnNilTip) :=
  wellFormedArcState_runArcCell arcBelowBaseForestState nilTipPath nilTipPath identityCellOnNilTip
    arcBelowBaseForestState_isWellFormed

/-! ## The joint simulation, re-stated over the bundle (residual (1), genuine consumption) -/

/-- ★ **The fold-level joint simulation over the bundle.**  The shipped `arcStepSimCount_processArcSpine`
threads BOTH the open-wire `sigma`-image (`openMap`) AND the fresh counter (`nfEq`) — together with
`rootComm` / `cupCorr` / `capCorr` / forests — across a whole spine, requiring the
`(freshSource, freshTarget, nonDegenerateSource)` triple as separate arguments.  Here that triple is
read off the two bundles ONCE: `wellFormedSource.isFresh` / `wellFormedTarget.isFresh` /
`wellFormedSource.isNonDegenerate`.  Genuine consumption of the r19-era fold lever — no re-derivation.
This IS residual (1): `openWires` and `nextFresh` transport jointly along `sigma`, now over the
bundle. -/
theorem arcStepSimCount_processArcSpine_ofWellFormed {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (isInjective : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (sigmaFixesZero : sigma 0 = 0)
    (atoms : List (SpineAtom signature sourceMode targetMode)) (stateSource stateTarget : ArcWireState)
    (wellFormedSource : WellFormedArcState stateSource) (wellFormedTarget : WellFormedArcState stateTarget)
    (fixesAbove : ∀ identifier, stateSource.nextFresh ≤ identifier → sigma identifier = identifier)
    (simulation : ArcStepSimCount sigma stateSource stateTarget) :
    ArcStepSimCount sigma (processArcSpine stateSource atoms) (processArcSpine stateTarget atoms) :=
  arcStepSimCount_processArcSpine sigma isInjective sigmaFixesZero atoms stateSource stateTarget
    wellFormedSource.isFresh wellFormedTarget.isFresh wellFormedSource.isNonDegenerate fixesAbove simulation

/-- ★ **The joint simulation over the bundle, at whole-cell granularity** — the same triple read off the
two bundles, feeding the shipped `arcStepSimCount_runArcCell`. -/
theorem arcStepSimCount_runArcCell_ofWellFormed {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (isInjective : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (sigmaFixesZero : sigma 0 = 0)
    (stateSource stateTarget : ArcWireState)
    (wellFormedSource : WellFormedArcState stateSource) (wellFormedTarget : WellFormedArcState stateTarget)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fixesAbove : ∀ identifier, stateSource.nextFresh ≤ identifier → sigma identifier = identifier)
    (simulation : ArcStepSimCount sigma stateSource stateTarget) :
    ArcStepSimCount sigma (runArcCell stateSource leftAcc rightAcc cell)
      (runArcCell stateTarget leftAcc rightAcc cell) :=
  arcStepSimCount_runArcCell sigma isInjective sigmaFixesZero stateSource stateTarget
    wellFormedSource.isFresh wellFormedTarget.isFresh wellFormedSource.isNonDegenerate
    leftAcc rightAcc cell fixesAbove simulation

/-! ## The compound-sigma joint per-step lever (residuals (1) + (3) + (4) tied) -/

/-- ★ **The cup-step joint lever at the r22 compound sigma.**  Instantiates the shipped whole-state
`stepCupArc_renameState` at `sigma := compoundFreshBlockTransposition baseFresh widthA widthB`,
discharging injectivity by r22's `compoundFreshBlockTransposition_injective` and `fixesAbove` by r22's
`compoundFreshBlockTransposition_fixesAbove` — GATED on the width seam
`baseFresh + widthA + widthB <= state.nextFresh` (residual (3)).  Because `renameState` renames
`openWires`, `links`, and events together while holding `nextFresh`, this single equation transports
the WHOLE state jointly (residual (1)) through one cup step. -/
theorem stepCupArc_renameState_compoundTransposition (baseFresh widthA widthB : Nat)
    (state : ArcWireState) (position : Nat)
    (seam : baseFresh + widthA + widthB ≤ state.nextFresh) :
    stepCupArc (renameState (compoundFreshBlockTransposition baseFresh widthA widthB) state) position
      = renameState (compoundFreshBlockTransposition baseFresh widthA widthB) (stepCupArc state position) :=
  stepCupArc_renameState (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    state position
    (fun identifier atLeastFresh =>
      compoundFreshBlockTransposition_fixesAbove baseFresh widthA widthB identifier
        (Nat.le_trans seam atLeastFresh))

/-- ★ **The cap-step joint lever at the r22 compound sigma.**  Same as the cup lever, additionally
discharging `sigmaFixesZero` (the cap's past-the-end wire-read default `0`) by r22's
`compoundFreshBlockTransposition_fixesZero` — GATED on `0 < baseFresh` (residual (4)) — alongside the
width seam (residual (3)).  Transports the whole state jointly (residual (1)) through one cap step. -/
theorem stepCapArc_renameState_compoundTransposition (baseFresh widthA widthB : Nat)
    (state : ArcWireState) (position : Nat)
    (basePositive : 0 < baseFresh)
    (seam : baseFresh + widthA + widthB ≤ state.nextFresh) :
    stepCapArc (renameState (compoundFreshBlockTransposition baseFresh widthA widthB) state) position
      = renameState (compoundFreshBlockTransposition baseFresh widthA widthB) (stepCapArc state position) :=
  stepCapArc_renameState (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    (compoundFreshBlockTransposition_fixesZero baseFresh widthA widthB basePositive)
    state position
    (fun identifier atLeastFresh =>
      compoundFreshBlockTransposition_fixesAbove baseFresh widthA widthB identifier
        (Nat.le_trans seam atLeastFresh))

/-! ## Firing probes — the joint lever on concrete instances (incl. the seam negative control) -/

/-- ★ **Positive joint-cup fire, seam satisfied.**  Base `2`, widths `(1,1)`, so the seam
`2 + 1 + 1 = 4 ≤ 4 = nextFresh` holds (`Nat.le_refl`).  The compound-sigma cup lever fires: the two run
orders coincide as WHOLE states through one cup step on `arcBelowBaseForestState`. -/
theorem arcJointCupFire_seamSatisfied :
    stepCupArc (renameState (compoundFreshBlockTransposition 2 1 1) arcBelowBaseForestState) 0
      = renameState (compoundFreshBlockTransposition 2 1 1) (stepCupArc arcBelowBaseForestState 0) :=
  stepCupArc_renameState_compoundTransposition 2 1 1 arcBelowBaseForestState 0 (Nat.le_refl _)

/-- The transported cup-reduct's open wires compute to `[4,5,3,2]` — a machine-checked snapshot of the
seam-satisfied joint fire (the committed-census value the fire realises). -/
theorem arcJointCupFire_openWires :
    (stepCupArc (renameState (compoundFreshBlockTransposition 2 1 1) arcBelowBaseForestState) 0).openWires
      = [4, 5, 3, 2] := rfl

/-- The transported cup-reduct's `nextFresh` computes to `7`. -/
theorem arcJointCupFire_nextFresh :
    (stepCupArc (renameState (compoundFreshBlockTransposition 2 1 1) arcBelowBaseForestState) 0).nextFresh
      = 7 := rfl

/-- The transported cup-reduct's links compute to `[(6,5),(4,5),(3,2)]`. -/
theorem arcJointCupFire_links :
    (stepCupArc (renameState (compoundFreshBlockTransposition 2 1 1) arcBelowBaseForestState) 0).links
      = [(6, 5), (4, 5), (3, 2)] := rfl

/-- A seam-VIOLATING fixture (the r23 probe shape): base `10`, widths `(2,3)`, but `nextFresh = 10 <
15 = baseFresh + widthA + widthB`, so the `fixesAbove` premise FAILS. -/
def arcSeamViolatingFixture : ArcWireState := ArcWireState.mk [0, 1] [(0, 1)] 10 0 [] []

/-- ★ **The seam-boundary NEGATIVE control (lever necessity).**  On the seam-violating fixture the two
run orders DIVERGE in their open wires: running-then-renaming renames the two fresh legs (`[13,14,0,1]`)
while renaming-then-running leaves them fresh (`[10,11,0,1]`).  Machine-checked inequality — the width
seam of `stepCupArc_renameState_compoundTransposition` is load-bearing, not decorative, and this is
exactly why r23 could ship only the unconditional LINKS lever and not the joint lever. -/
theorem arcSeamViolation_openWiresDiffer :
    (stepCupArc (renameState (compoundFreshBlockTransposition 10 2 3) arcSeamViolatingFixture) 0).openWires
      ≠ (renameState (compoundFreshBlockTransposition 10 2 3) (stepCupArc arcSeamViolatingFixture 0)).openWires := by
  decide

end FX1Poly.Polygraph
