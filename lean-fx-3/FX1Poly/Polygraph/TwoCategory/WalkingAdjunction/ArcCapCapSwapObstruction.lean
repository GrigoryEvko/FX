import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # WalkingAdjunction/ArcCapCapSwapObstruction — the CAP x CAP renaming route is FALSE

**The finding (the fourth combo breaks the renaming vehicle).**  The three shipped two-step
`ArcStepSimCount` simulations (CUP x CUP `arcStepSimCount_cupCupSwap`, CUP x CAP
`arcStepSimCount_cupCapSwap`, CAP x CUP `arcStepSimCount_capCupSwap`) suggested a fourth: CAP x CAP
under `arcFreshBlockTransposition state.nextFresh 1 1`.  That statement — and EVERY `sigma`, not
just the fresh-block transposition — is FALSE.  A cap redirects the LEFT wire's component root onto
the RIGHT wire's root, so running two caps in the two orders composes two OLD-node root
redirections in opposite orders.  When the two cap windows touch OVERLAPPING components, the final
union-find representative of the merged component is order-dependent: the low-first order parks it
at the high pair's old root, the high-first order at the low pair's old root.  No renaming can
reconcile them, because the divergent representative can be pinned by an OPEN wire (`openMap` /
`bnodeCorr` force `sigma` to fix it) while the per-root event counts then disagree at that pinned
root (`capCorr` reads `2 = 0`).

**The concrete fixture** (machine-evaluated below): wires `[3, 5, 6, 4, 7]` with prior cup pairs
`3 ~ 4` (parent edge `(3,4)`) and `5 ~ 6` (parent edge `(5,6)`), `nextFresh = 8`.  The low cap eats
`(3, 5)` at position `0`; the high cap eats `(4, 7)` at window gap `1` — disjoint windows `{0,1}`
and `{3,4}`, the exact shape the Godement bubbling swap fires on, and `3 ~ 4` makes the two windows'
components overlap.  Low-first drives every merged root to `7`; high-first drives every merged root
to `6` — and `6` is the surviving OPEN wire.  All four side-conditions of the would-be simulation
(freshness, forest, positive `nextFresh`, window bound) HOLD (`capCapObstruction_meetsSwapSideConditions`),
so the refutation kills the exact candidate statement, not a degenerate edge case.

**What survives.**  The partition view is order-INSENSITIVE: the two orders are `SameArcPartition`
(`capCapObstruction_sameArcPartition`) and their arc extracts are EQUAL
(`capCapObstruction_extract_eq`) — each boundary port counts its own component's turnbacks, and the
divergent representative cancels out of every per-port read.  So the SAT-ARC-REC peel's CAP x CAP
leg must ride a STATE-AGREEMENT vehicle (equal open wires / fresh counter / loops / event lists +
partition-equal links — all order-insensitive and step-stable), not the `ArcStepSimCount` /
`ArcRenameRel` renaming vehicle; the W9 residual-(2) "general block-swap `sigma` over arbitrary
cells" is hereby REFUTED in its renaming form for cap-cap pairs and re-scoped to the three
heterogeneous combos.

Zero-axiom: everything computes on concrete states; the only tactics are `decide`, `injection`,
`rw`, `cases`, and constructor introduction. -/

namespace FX1Poly.Polygraph

/-- The obstruction's starting state: open wires `[3, 5, 6, 4, 7]`, prior cup links `3 ~ 4` and
`5 ~ 6`, `nextFresh = 8`.  The low cap window `{0, 1}` reads `(3, 5)`; the high cap window `{3, 4}`
reads `(4, 7)`; the windows are disjoint but `3 ~ 4` overlaps their components. -/
def capCapObstructionStart : ArcWireState :=
  ArcWireState.mk [3, 5, 6, 4, 7] [(3, 4), (5, 6)] 8 0 [] []

/-- The LOW-FIRST run order: cap at `positionLow = 0`, then cap at `gap + positionLow = 1 + 0` —
the `stateS` of the would-be CAP x CAP `ArcStepSimCount` statement at `gap = 1`, `positionLow = 0`.
Every merged root lands at `7`. -/
def capCapObstructionLowFirst : ArcWireState :=
  stepCapArc (stepCapArc capCapObstructionStart 0) (1 + 0)

/-- The HIGH-FIRST run order: cap at `gap + 2 + positionLow = 1 + 2 + 0`, then cap at
`positionLow = 0` — the `stateT` of the would-be statement.  Every merged root lands at `6`, the
surviving OPEN wire. -/
def capCapObstructionHighFirst : ArcWireState :=
  stepCapArc (stepCapArc capCapObstructionStart (1 + 2 + 0)) 0

/-- **Non-degeneracy: the fixture satisfies every side-condition of the would-be CAP x CAP
simulation** — `ArcStateFresh`, the forest shape, `0 < nextFresh`, and the disjoint-window bound
`gap + positionLow + 2 ≤ length` at `gap = 1`, `positionLow = 0`.  So the refutations below kill
the fully-hypothesized candidate statement, not a degenerate instance. -/
theorem capCapObstruction_meetsSwapSideConditions :
    ArcStateFresh capCapObstructionStart
      ∧ isUnionFindForest capCapObstructionStart.links
      ∧ 0 < capCapObstructionStart.nextFresh
      ∧ 1 + 0 + 2 ≤ capCapObstructionStart.openWires.length := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, by decide, by decide⟩
  · intro wire wireMember
    cases wireMember with
    | head => decide
    | tail _ memberOne =>
      cases memberOne with
      | head => decide
      | tail _ memberTwo =>
        cases memberTwo with
        | head => decide
        | tail _ memberThree =>
          cases memberThree with
          | head => decide
          | tail _ memberFour =>
            cases memberFour with
            | head => decide
            | tail _ memberFive => cases memberFive
  · intro edge edgeMember
    cases edgeMember with
    | head => exact ⟨by decide, by decide⟩
    | tail _ memberOne =>
      cases memberOne with
      | head => exact ⟨by decide, by decide⟩
      | tail _ memberTwo => cases memberTwo
  · intro node nodeMember; cases nodeMember
  · intro node nodeMember; cases nodeMember
  · show isUnionFindForest [(3, 4), (5, 6)]
    exact ⟨rfl, rfl, by decide, rfl, rfl, by decide, trivial⟩

/-- ★ **The CAP x CAP `ArcStepSimCount` is FALSE — for EVERY `sigma`.**  `openMap` reads
`[6] = [sigma 6]`, pinning `sigma 6 = 6` (the divergent representative `6` survives as an OPEN
wire).  Then `capCorr` at root `6` reads `2 = 0`: the high-first order roots BOTH cap events at
`6`, the low-first order roots both at `7`.  So the fourth combo of the two-step swap kit cannot
be closed by any renaming — the vehicle, not the target, is what fails (the extracts of the two
orders are EQUAL, `capCapObstruction_extract_eq`). -/
theorem not_arcStepSimCount_capCapOverlap :
    ∀ sigma : Nat → Nat,
      ¬ ArcStepSimCount sigma capCapObstructionLowFirst capCapObstructionHighFirst := by
  intro sigma sim
  have openPin : ([6] : List Nat) = sigma 6 :: [] := sim.openMap
  injection openPin with sigmaSixPinned _
  have capCount := sim.capCorr 6
  rw [← sigmaSixPinned] at capCount
  exact absurd capCount (by decide)

/-- ★ **The CAP x CAP `ArcRenameRel` is FALSE — for EVERY `sigma`** (the same obstruction at the
readout level): `bnodeCorr` at the sole boundary port pins `sigma 6 = 6`, and `capCorr` at root
`6` again reads `2 = 0`.  So the suffix-peel's renaming readout is equally unavailable for the
cap-cap swap. -/
theorem not_arcRenameRel_capCapOverlap :
    ∀ sigma : Nat → Nat,
      ¬ ArcRenameRel 0 sigma capCapObstructionLowFirst capCapObstructionHighFirst := by
  intro sigma rel
  have sigmaSixPinned : (6 : Nat) = sigma 6 := rel.bnodeCorr 0 (by decide)
  have capCount := rel.capCorr 6
  rw [← sigmaSixPinned] at capCount
  exact absurd capCount (by decide)

/-- **The partition view survives the obstruction**: the two run orders are `SameArcPartition` —
equal open-wire count, equal loops, the same boundary same-component booleans, and the same
per-port cup/cap turnback counts (each port counts its OWN component's events, so the divergent
representative cancels: both orders count `2` cap turnbacks on the surviving strand). -/
theorem capCapObstruction_sameArcPartition :
    SameArcPartition 0 capCapObstructionLowFirst capCapObstructionHighFirst := by
  refine ⟨rfl, by decide, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex firstBound secondBound
    have firstSmall : firstIndex < 1 := firstBound
    have secondSmall : secondIndex < 1 := secondBound
    have firstZero : firstIndex = 0 :=
      Nat.le_antisymm (Nat.le_of_lt_succ firstSmall) (Nat.zero_le firstIndex)
    have secondZero : secondIndex = 0 :=
      Nat.le_antisymm (Nat.le_of_lt_succ secondSmall) (Nat.zero_le secondIndex)
    subst firstZero; subst secondZero
    decide
  · intro index indexBound
    have indexSmall : index < 1 := indexBound
    have indexZero : index = 0 :=
      Nat.le_antisymm (Nat.le_of_lt_succ indexSmall) (Nat.zero_le index)
    subst indexZero
    decide
  · intro index indexBound
    have indexSmall : index < 1 := indexBound
    have indexZero : index = 0 :=
      Nat.le_antisymm (Nat.le_of_lt_succ indexSmall) (Nat.zero_le index)
    subst indexZero
    decide

/-- ★ **The arc extracts of the two orders are EQUAL** — the reconstruction target itself is
order-insensitive at the obstruction fixture.  The refutations above therefore indict only the
renaming VEHICLE: the CAP x CAP leg of the swap kit must be carried by order-insensitive state
agreement (equal wires / counters / event lists + partition-equal links), not by
`ArcStepSimCount`. -/
theorem capCapObstruction_extract_eq :
    extractArc 0 capCapObstructionLowFirst = extractArc 0 capCapObstructionHighFirst :=
  extractArc_eq_of_sameArcPartition 0 capCapObstructionLowFirst capCapObstructionHighFirst
    capCapObstruction_sameArcPartition rfl rfl

/-- **Honesty marker — the CAP x CAP renaming obstruction is ESTABLISHED.**
`not_arcStepSimCount_capCapOverlap` / `not_arcRenameRel_capCapOverlap` prove that NO renaming
`sigma` relates the two run orders of a disjoint-window cap-cap swap at the (fresh, forest,
non-degenerate, in-bounds) fixture `capCapObstructionStart` — overlapping components make the
merged component's union-find representative order-dependent, and an open wire pins it.  The W9
residual-(2) "general block-swap `sigma` over arbitrary cells" is therefore FALSE in its renaming
form: it is re-scoped to the three heterogeneous combos (CUP x CUP / CUP x CAP / CAP x CUP, all
shipped), and the CAP x CAP leg rides the state-agreement vehicle
(`capCapObstruction_sameArcPartition` / `capCapObstruction_extract_eq` exhibit the surviving
order-insensitive content).  `= true` records the obstruction, NOT a claim that cap-cap
simulation is closed. -/
def fxMode_hasCapCapRenameObstruction : Bool := true

end FX1Poly.Polygraph
