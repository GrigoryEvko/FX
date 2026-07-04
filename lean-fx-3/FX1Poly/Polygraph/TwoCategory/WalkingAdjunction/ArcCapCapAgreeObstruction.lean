import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStateAgreement

/-! # WalkingAdjunction/ArcCapCapAgreeObstruction — plain state agreement ALSO fails for CAP x CAP

**The second cap-cap obstruction (the disjoint-component face).**  The first obstruction
(`ArcCapCapSwapObstruction`) killed the RENAMING vehicle at an overlapping-component fixture.
This file kills the PLAIN state-agreement vehicle (`ArcStateAgree`, `sigma = identity`) at the
opposite, disjoint-component fixture: the two run orders allocate their cap event nodes in the
same order (`nf` first, `nf + 1` second) but attach them to SWAPPED components — low-first puts
`nf` in the LOW pair's component, high-first puts `nf` in the HIGH pair's component.  When the two
components stay disjoint, `componentsEq` fails at the pair (event node, low wire).

**The concrete fixture** (machine-evaluated below): wires `[0, 1, 2, 3]`, empty links,
`nextFresh = 4`; low cap window `{0, 1}`, high cap window `{2, 3}` (`positionLow = 0`, `gap = 0`).
Low-first: event `4` joins `{0, 1}`, event `5` joins `{2, 3}`.  High-first: event `4` joins
`{2, 3}`, event `5` joins `{0, 1}`.  `isSameComponent links 4 0` is `true` in the first and
`false` in the second.

**The corrected target.**  Together the two obstructions bracket the cap-cap swap exactly:

  * the renaming vehicle fails because OLD-node representatives diverge (overlap face);
  * the plain-agreement vehicle fails because EVENT-node attachments swap (disjoint face);
  * what both fixtures satisfy is the `sigma`-TWISTED PARTITION simulation — `sigma` the
    event-block transposition (`nf <-> nf + 1`), with `isSameComponent stateT.links (sigma x)
    (sigma y) = isSameComponent stateS.links x y` in place of the root-level `rootComm` and
    per-probe (port-rooted) event counts in place of the per-root counts.  That relation reads
    representatives never, tolerates the event swap by construction, is implied by
    `ArcStepSimCount` on the three shipped heterogeneous combos (via `rootComm` + injectivity),
    and still reads out to `SameArcPartition` — the corrected fourth-combo route.

Zero-axiom: concrete states, `decide`-computed reads. -/

namespace FX1Poly.Polygraph

/-- The disjoint-component fixture: four parentless wires, empty links, `nextFresh = 4`.  The two
cap windows `{0, 1}` and `{2, 3}` touch components that stay disjoint through both runs. -/
def capCapDisjointStart : ArcWireState :=
  ArcWireState.mk [0, 1, 2, 3] [] 4 0 [] []

/-- LOW-FIRST: cap at `positionLow = 0`, then cap at `gap + positionLow = 0` — event `4` lands in
the `{0, 1}` component, event `5` in the `{2, 3}` component. -/
def capCapDisjointLowFirst : ArcWireState :=
  stepCapArc (stepCapArc capCapDisjointStart 0) 0

/-- HIGH-FIRST: cap at `gap + 2 + positionLow = 2`, then cap at `positionLow = 0` — event `4`
lands in the `{2, 3}` component, event `5` in the `{0, 1}` component: the attachments SWAP. -/
def capCapDisjointHighFirst : ArcWireState :=
  stepCapArc (stepCapArc capCapDisjointStart 2) 0

/-- **Non-degeneracy: the fixture satisfies every side-condition of the would-be cap-cap
agreement** — freshness, the (empty, trivial) forest, positive `nextFresh`, and the
disjoint-window bound at `gap = 0`, `positionLow = 0`. -/
theorem capCapDisjoint_meetsSwapSideConditions :
    ArcStateFresh capCapDisjointStart
      ∧ isUnionFindForest capCapDisjointStart.links
      ∧ 0 < capCapDisjointStart.nextFresh
      ∧ 0 + 0 + 2 ≤ capCapDisjointStart.openWires.length := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, isUnionFindForest_nil, by decide, by decide⟩
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
          | tail _ memberFour => cases memberFour
  · intro edge edgeMember; cases edgeMember
  · intro node nodeMember; cases nodeMember
  · intro node nodeMember; cases nodeMember

/-- ★ **The two cap-cap run orders are NOT `ArcStateAgree`** — the plain (identity-renaming)
state-agreement vehicle fails on the disjoint face: `componentsEq` at the pair (event node `4`,
low wire `0`) reads `true = false`, because the two orders attach event `4` to different
components.  Together with `not_arcStepSimCount_capCapOverlap` (no renaming works on the overlap
face) this pins the corrected cap-cap target as the `sigma`-twisted partition simulation. -/
theorem not_arcStateAgree_capCapDisjoint :
    ¬ ArcStateAgree capCapDisjointLowFirst capCapDisjointHighFirst := by
  intro agree
  have componentMismatch := agree.componentsEq 4 0
  exact absurd componentMismatch (by decide)

/-- **Honesty marker — the plain-agreement obstruction is ESTABLISHED.**  The cap-cap swap
satisfies NEITHER shipped vehicle pointwise: `ArcStepSimCount`/`ArcRenameRel` fail at the
overlapping-component fixture (`fxMode_hasCapCapRenameObstruction`), and `ArcStateAgree` fails at
the disjoint-component fixture (`not_arcStateAgree_capCapDisjoint`).  The corrected route is the
`sigma`-twisted partition simulation (componentsCorr + per-probe counts under the event
transposition), for which `ArcStateAgree`'s join-congruence crux and readout remain the
substrate.  `= true` records the obstruction, NOT a claim that the twisted simulation is built. -/
def fxMode_hasCapCapAgreeObstruction : Bool := true

end FX1Poly.Polygraph
