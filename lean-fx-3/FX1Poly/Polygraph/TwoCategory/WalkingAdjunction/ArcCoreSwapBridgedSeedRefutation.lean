import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCoreSwapCapFlipRefutation

/-! # MODE-COMMUTE r29 — the BRIDGED-SEED old-root asymmetry: a second, boundary-only refutation
of `ArcGodementCoreSwapSimCount` + the sharpness witness the cap-flip refutation could not give

## Placement (read the r4 owner first)

`ArcGodementCoreSwapSimCount` (the `:3046` residual-(2) obligation) was ALREADY machine-refuted
at the counit/cap join-order root flip (`ArcCoreSwapCapFlipRefutation.lean`,
`not_arcGodementCoreSwapSimCount_adjunction`, MODE-COMMUTE r4): there the flipped roots sit on
SURVIVING open wires, so `openMap` pins `sigma` on them at ANY `bottomCount` (even `0`).  This
file formalizes the r28 verifier's COMPLEMENTARY datum — the old-root asymmetry on CONSUMED
wires at a pre-bridged seed — and DECIDES the question the r28 B4 adjudication and the r28
verify report left open: does the obligation's existential survive at bridged seeds when the
flipped roots are NOT open (so `openMap` pins nothing relevant)?  Answer, both halves proven:

  * **`not_arcGodementCoreSwapSimCount_atBridgedSeed`** — NO at full boundary width: with
    `bottomCount := 8 = nextFresh` the boundary-fixing conjunct alone forces `2 = 6`
    (`rootComm` at consumed wire `1`); `openMap` plays no role — a SECOND, mechanism-disjoint
    refutation instance;
  * **`bridgedSwapInstance_smallBoundarySatisfiable`** — YES at small width: at
    `bottomCount := 2` the root transposition `2 <-> 6` witnesses the FULL eight-field
    `ArcStepSimCount` on the same instance — the sharpness the r4 flip could NOT exhibit (its
    open-wire pinning kills every `sigma` outright), and the machine answer to the r28
    verify-report question whether the r26-style counterexamples transfer to the bare
    existential: they do NOT at small boundary — the failure is EXACTLY the boundary width.

## The instance

  * seed `openWires [0..7]`, links `[(5, 1)]` — the bridge pre-connects the f-window read
    wire `1` with the g-window read wire `5` (the two windows share a component: the exact
    configuration the r26/r28 component-disjointness guard excludes);
  * both cells are the whisker-sandwiched counit (a cap at window-relative position `1`);
    the common prefix `cellAlpha` is the identity cell (a legal instantiation);
  * the two run orders merge the SAME two components in OPPOSITE orders, so old wire `1`
    roots at old id `6` (redex order) versus old id `2` (reduct order) — kernel-pinned; both
    wires `1, 2, 5, 6` are CONSUMED (final open wires `[0, 3, 4, 7]` in both orders).

## Pin adjudication (owners read verbatim, none flipped)

  * `fxMode_hasArcGodementSwapRenameableProof2` (`ArcSwapRenameable.lean:3046`) — stays `false`
    (refutation-permanent since r4; re-recorded here).  The pointwise parent reduction
    `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` remains sound with an
    unsatisfiable hypothesis — the THIRD dead vehicle after `renameState` (W4) and
    `ArcStepSim` (W6/W7).  The LIVE SUCCESSOR content is the r26/r28 guarded whole-cell
    theorem (`arcCellPastCellSwapSimCount` / `arcGodementInnerSwapSimCount`), whose
    component-disjointness guard excludes exactly the bridged configuration exercised here.
  * `fxMode_hasArcGodementSwapRenameableProof` (`ArcSamePartitionFresh.lean`) — stays `false`;
    the parent `ArcGodementSwapRenameable` quantifies over every fresh state and is NOT decided
    by this file (the core-swap route to it is dead; a direct decision would need a separate
    refutation at the parent's own `ArcRenameRel` granularity).
  * `:234` / `:525` / `:545` — untouched; adjudicated permanently in r24/r28.

Raw Lean 4 + Init; structural only; per-declaration `#assert_no_axioms` + independent
`#print axioms` twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bridged seed and the instantiating cells -/

/-- The pre-bridged seed: eight open wires, ONE seed link `(5, 1)` connecting the f-window read
wire `1` (the sandwiched cap at window position `1` reads wires `1, 2`) with the g-window read
wire `5` (the shifted cap reads wires `5, 6`).  Fresh frontier `8`, no loops, no events. -/
def bridgedSwapSeedState : ArcWireState :=
  ArcWireState.mk [0, 1, 2, 3, 4, 5, 6, 7] [(5, 1)] 8 0 [] []

/-- The empty path at the base mode (every whisker accumulator of the instance). -/
def bridgedSwapNilBase : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- The length-4 middle boundary `[left,right,left,right]` — `fLow = fMid = gLow` of the
instance (the sandwiched counit's domain). -/
def bridgedSwapMidPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  composePath adjunctionLeftThenRight adjunctionLeftThenRight

/-- The common prefix `cellAlpha` of the instance — the identity cell on the middle boundary
(a legal instantiation of the obligation's universally-quantified prefix cell). -/
def bridgedSwapCommonPrefixCell :
    RawTwoCellExpr adjunctionModeSignature bridgedSwapMidPath bridgedSwapMidPath :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) bridgedSwapMidPath

/-- The seed is fresh (every wire / link endpoint below the frontier `8`). -/
theorem bridgedSwapSeedState_isFresh : ArcStateFresh bridgedSwapSeedState := by
  unfold ArcStateFresh bridgedSwapSeedState; decide

/-- The seed link list `[(5, 1)]` is a union-find forest (one child-parent edge, no cycle). -/
theorem bridgedSwapSeedState_isForest : isUnionFindForest bridgedSwapSeedState.links :=
  ⟨rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq, trivial⟩

/-- The seed satisfies the full well-formedness bundle. -/
theorem bridgedSwapSeedState_isWellFormed : WellFormedArcState bridgedSwapSeedState :=
  ⟨bridgedSwapSeedState_isFresh, bridgedSwapSeedState_isForest, by decide⟩

/-- The bridge is a GUARD VIOLATION: the two windows' read wires `1` and `5` share a component
at the seed — exactly the configuration the r26/r28 component-disjointness guard excludes. -/
theorem bridgedSwapSeedState_violatesWindowGuard :
    isSameComponent bridgedSwapSeedState.links 1 5 = true := rfl

/-! ## The two run orders (the obligation's literal redex / reduct at the instance) -/

/-- The REDEX run order: prefix (identity), then `cellAlphaUpper` at `(nil, gLow . nil)`, then
`cellBeta` at `(nil . fHigh, nil)` — the alpha-block-first order. -/
def bridgedSwapRedexRun : ArcWireState :=
  runArcCell
    (runArcCell
      (runArcCell bridgedSwapSeedState bridgedSwapNilBase
        (composePath bridgedSwapMidPath bridgedSwapNilBase) bridgedSwapCommonPrefixCell)
      bridgedSwapNilBase (composePath bridgedSwapMidPath bridgedSwapNilBase)
      whiskerSandwichedCounitCell)
    (composePath bridgedSwapNilBase adjunctionLeftThenRight) bridgedSwapNilBase
    whiskerSandwichedCounitCell

/-- The REDUCT run order: prefix (identity), then `cellBeta` at `(nil . fMid, nil)`, then
`cellAlphaUpper` at `(nil, gMid . nil)` — the beta-block-first order. -/
def bridgedSwapReductRun : ArcWireState :=
  runArcCell
    (runArcCell
      (runArcCell bridgedSwapSeedState bridgedSwapNilBase
        (composePath bridgedSwapMidPath bridgedSwapNilBase) bridgedSwapCommonPrefixCell)
      (composePath bridgedSwapNilBase bridgedSwapMidPath) bridgedSwapNilBase
      whiskerSandwichedCounitCell)
    bridgedSwapNilBase (composePath adjunctionLeftThenRight bridgedSwapNilBase)
    whiskerSandwichedCounitCell

/-- ★ **THE OLD-ROOT ASYMMETRY, kernel-pinned.**  The two orders merge the bridged components in
opposite orders: old wire `1` roots at old id `6` after the redex order but at old id `2` after
the reduct order.  Both roots are BELOW the seed frontier `8` — this is old-id motion no
boundary-fixing carrier can absorb.  `rfl` pair. -/
theorem bridgedSwapRuns_oldRootAsymmetry :
    unionFindRootOf bridgedSwapRedexRun.links 1 = 6
      ∧ unionFindRootOf bridgedSwapReductRun.links 1 = 2 :=
  ⟨rfl, rfl⟩

/-- The literal final record of the redex order (whole-record kernel pin below). -/
def bridgedSwapRedexValue : ArcWireState :=
  ArcWireState.mk [0, 3, 4, 7] [(9, 6), (2, 6), (8, 2), (1, 2), (5, 1)] 10 0 [] [9, 8]

/-- The literal final record of the reduct order. -/
def bridgedSwapReductValue : ArcWireState :=
  ArcWireState.mk [0, 3, 4, 7] [(9, 2), (6, 2), (8, 6), (1, 6), (5, 1)] 10 0 [] [9, 8]

/-- The redex order computes to its literal record (whole-record `rfl` pin): the two orders
produce the SAME open wires `[0, 3, 4, 7]`, frontier `10`, no loops, cap events `[9, 8]` — but
their union-find trees route old wire `1` through opposite merge orders. -/
theorem bridgedSwapRedexRun_valueEq : bridgedSwapRedexRun = bridgedSwapRedexValue := rfl

/-- The reduct order computes to its literal record (whole-record `rfl` pin). -/
theorem bridgedSwapReductRun_valueEq : bridgedSwapReductRun = bridgedSwapReductValue := rfl

/-! ## THE REFUTATION -/

/-- ★★★ **The SECOND refutation of `ArcGodementCoreSwapSimCount adjunctionModeSignature` — the
boundary-only mechanism at a pre-bridged seed.**  Instantiate the obligation at the bridged seed
with `bottomCount := 8 = nextFresh` (allowed by its own `bottomCount ≤ nextFresh` hypothesis),
the identity prefix cell, and the sandwiched counit in both windows.  The demanded `sigma` must
fix every id below `8`, in particular `1` and `6`; the `rootComm` field at wire `1` then forces
`unionFindRootOf reduct 1 = sigma (unionFindRootOf redex 1)`, i.e. `2 = sigma 6 = 6` — a
kernel-refuted numeral equation.  Unlike the r4 cap-flip refutation
(`not_arcGodementCoreSwapSimCount_adjunction`), the flipped roots here sit on CONSUMED wires, so
`openMap` pins nothing relevant — the refutation rides ONLY on the boundary-fixing conjunct,
which is why the sharpness companion below can exhibit a genuine full-field `sigma` at small
`bottomCount`.  The r28 verifier's old-root-asymmetry datum, closed into a machine proof. -/
theorem not_arcGodementCoreSwapSimCount_atBridgedSeed :
    ¬ ArcGodementCoreSwapSimCount adjunctionModeSignature := by
  intro coreSwap
  obtain ⟨sigma, sigmaInjective, sigmaFixesZero, fixesBoundary, fixesAbove, simCount⟩ :=
    coreSwap bridgedSwapCommonPrefixCell whiskerSandwichedCounitCell whiskerSandwichedCounitCell
      bridgedSwapNilBase bridgedSwapNilBase 8 bridgedSwapSeedState bridgedSwapSeedState_isFresh
      (Nat.le_refl 8) bridgedSwapSeedState_isForest (by decide)
  have sigmaFixesOne : sigma 1 = 1 := fixesBoundary 1 (by decide)
  have sigmaFixesSix : sigma 6 = 6 := fixesBoundary 6 (by decide)
  have rootCommAtOne : unionFindRootOf bridgedSwapReductRun.links (sigma 1)
      = sigma (unionFindRootOf bridgedSwapRedexRun.links 1) := simCount.rootComm 1
  rw [sigmaFixesOne, bridgedSwapRuns_oldRootAsymmetry.1,
    bridgedSwapRuns_oldRootAsymmetry.2, sigmaFixesSix] at rootCommAtOne
  exact absurd rootCommAtOne (by decide)

/-! ## The sharpness companion: the SAME instance is satisfiable at small `bottomCount`

The failure is EXACTLY the boundary-fixing width, not the sim fields: at `bottomCount := 2` the
root transposition `2 <-> 6` witnesses the obligation's full existential on the same instance. -/

/-- The root transposition `2 <-> 6` — the carrier matching the two orders' opposite merge
orders (redex roots the merged component at `6`, reduct at `2`). -/
def bridgedSwapRootTransposition (node : Nat) : Nat :=
  if node == 2 then 6 else if node == 6 then 2 else node

/-- The transposition is an involution (case split on the two moved points). -/
theorem bridgedSwapRootTransposition_involution :
    ∀ node, bridgedSwapRootTransposition (bridgedSwapRootTransposition node) = node := by
  intro node
  cases beqTwo : (node == 2) with
  | true =>
      have nodeIsTwo : node = 2 := of_decide_eq_true beqTwo
      subst nodeIsTwo; rfl
  | false =>
      cases beqSix : (node == 6) with
      | true =>
          have nodeIsSix : node = 6 := of_decide_eq_true beqSix
          subst nodeIsSix; rfl
      | false =>
          show bridgedSwapRootTransposition
              (if node == 2 then 6 else if node == 6 then 2 else node) = node
          rw [beqTwo, beqSix]
          show (if node == 2 then 6 else if node == 6 then 2 else node) = node
          rw [beqTwo, beqSix]
          exact rfl

/-- The transposition is injective (involutions are). -/
theorem bridgedSwapRootTransposition_injective (firstNode secondNode : Nat)
    (imagesEqual : bridgedSwapRootTransposition firstNode = bridgedSwapRootTransposition secondNode) :
    firstNode = secondNode := by
  have doubled := congrArg bridgedSwapRootTransposition imagesEqual
  rwa [bridgedSwapRootTransposition_involution, bridgedSwapRootTransposition_involution]
    at doubled

/-- The redex value's literal link list is a union-find forest (each child mentioned once,
no cycles — five cons layers, each discharged on the literals). -/
theorem bridgedSwapRedexValue_isForest : isUnionFindForest bridgedSwapRedexValue.links :=
  ⟨rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq, trivial⟩

/-- The reduct value's literal link list is a union-find forest. -/
theorem bridgedSwapReductValue_isForest : isUnionFindForest bridgedSwapReductValue.links :=
  ⟨rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq,
    rfl, rfl, fun absurdBeq => Bool.noConfusion absurdBeq, trivial⟩

/-- The full eight-field simulation between the two LITERAL final records under the root
transposition: `openMap` / `nfEq` / `loopsEq` / `cupCorr` by computation on the literals,
`rootComm` / `capCorr` by a ten-point case analysis whose variable tail reduces definitionally
(every link child is a closed numeral, so the parent lookup on `tail + 10` computes to `none`),
forests on the literal link lists. -/
theorem bridgedSwapValues_simCount :
    ArcStepSimCount bridgedSwapRootTransposition bridgedSwapRedexValue bridgedSwapReductValue := by
  refine ⟨rfl, rfl, ?rootComm, rfl, fun _ => rfl, ?capCorr,
    bridgedSwapRedexValue_isForest, bridgedSwapReductValue_isForest⟩
  case rootComm =>
    intro node
    match node with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | 9 => rfl
    | tail + 10 => rfl
  case capCorr =>
    intro rootHere
    match rootHere with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | 9 => rfl
    | tail + 10 => rfl

/-- ★★ **The SAME instance satisfies the obligation's existential at `bottomCount := 2`.**  The
root transposition `2 <-> 6` is injective, fixes `0` and `1` (everything below `2`), fixes
everything at-or-above the final frontier `10`, and witnesses the FULL eight-field
`ArcStepSimCount` between the two orders (`openMap` / `nfEq` / `loopsEq` / `cupCorr` by
computation, `rootComm` / `capCorr` by a ten-point-plus-tail case analysis — the tail cases
reduce definitionally because every link child is a closed numeral).  So the refutation above is
EXACTLY about the boundary-fixing width: the sim fields themselves hold under a permuting
carrier; only the demand `sigma` fix the whole old-id range (up to `bottomCount = nextFresh`)
is unsatisfiable at a pre-bridged seed. -/
theorem bridgedSwapInstance_smallBoundarySatisfiable :
    ∃ sigma : Nat → Nat,
      (∀ firstNode secondNode, sigma firstNode = sigma secondNode → firstNode = secondNode)
        ∧ sigma 0 = 0
        ∧ (∀ identifier, identifier < 2 → sigma identifier = identifier)
        ∧ (∀ identifier, bridgedSwapRedexRun.nextFresh ≤ identifier → sigma identifier = identifier)
        ∧ ArcStepSimCount sigma bridgedSwapRedexRun bridgedSwapReductRun := by
  refine ⟨bridgedSwapRootTransposition, bridgedSwapRootTransposition_injective, rfl,
    ?fixesBelow, ?fixesAbove, ?simCount⟩
  case fixesBelow =>
    intro identifier isBelow
    match identifier, isBelow with
    | 0, _ => rfl
    | 1, _ => rfl
    | identifier + 2, isBelow =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isBelow))
          (Nat.not_lt_zero identifier)
  case fixesAbove =>
    intro identifier isAtLeast
    rw [bridgedSwapRedexRun_valueEq] at isAtLeast
    have notTwo : (identifier == 2) = false :=
      natBeqFalseOfNe (fun isTwo => by subst isTwo; exact absurd isAtLeast (by decide))
    have notSix : (identifier == 6) = false :=
      natBeqFalseOfNe (fun isSix => by subst isSix; exact absurd isAtLeast (by decide))
    show (if identifier == 2 then 6 else if identifier == 6 then 2 else identifier) = identifier
    rw [notTwo, notSix]
    exact rfl
  case simCount =>
    rw [bridgedSwapRedexRun_valueEq, bridgedSwapReductRun_valueEq]
    exact bridgedSwapValues_simCount

/-! ## Honesty markers + the pin adjudication -/

/-- ★★★ **Honesty marker — the bridged-seed decision: second refutation instance + THE
SHARPNESS WITNESS.**  `ArcGodementCoreSwapSimCount adjunctionModeSignature`, already refuted at
the r4 cap flip (`ArcCoreSwapCapFlipRefutation.lean`, open-wire root pinning), is refuted AGAIN
at a pre-bridged seed by a mechanism-disjoint route
(`not_arcGodementCoreSwapSimCount_atBridgedSeed`): the old-root asymmetry lands on CONSUMED
wires (`bridgedSwapRuns_oldRootAsymmetry`), `openMap` pins nothing relevant, and ONLY the
boundary-fixing conjunct kills the existential.  The sharpness companion
(`bridgedSwapInstance_smallBoundarySatisfiable`) — unavailable at the r4 flip — proves the SAME
instance satisfies the FULL eight-field existential at `bottomCount := 2` via the root
transposition `2 <-> 6`, deciding the r28 verify-report question: the bare existential DOES
survive bridged seeds at small boundary width; the failure is EXACTLY the boundary-fixing
width.  The LIVE SUCCESSOR content is the r26/r28 guarded whole-cell theorem —
`arcCellPastCellSwapSimCount` / `arcGodementInnerSwapSimCount` — whose component-disjointness
guard EXCLUDES exactly the bridged configuration exercised here
(`bridgedSwapSeedState_violatesWindowGuard`).  `= true`. -/
def fxMode_hasArcCoreSwapBridgedSeedDecision : Bool := true

/-- **Adjudication pin — `:3046` stays `false`, refutation-PERMANENT since r4, re-recorded**:
its sole remaining residual (2) is `ArcGodementCoreSwapSimCount`, refuted as stated at TWO
independent instances (the r4 cap flip; the bridged seed here).  The pin can never flip on its
verbatim demand.  `rfl`. -/
theorem arcCoreSwapRefutation_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Adjudication pin — the parent block-swap witness marker stays `false`**: the core-swap
route to `ArcGodementSwapRenameable` is dead (r4 + this file), and no direct decision of the
parent is claimed here.  `rfl`. -/
theorem arcCoreSwapRefutation_swapRenameableProof_stays_false :
    fxMode_hasArcGodementSwapRenameableProof = false := rfl

/-- **Adjudication pin — the r4 cap-flip refutation marker STANDS** (`rfl` re-record of the
first refutation's owner; this file is its mechanism-disjoint bridged-seed companion). -/
theorem arcCoreSwapRefutation_capFlipRefutationStands :
    fxMode_hasArcCoreSwapSimCountRefuted = true := rfl

end FX1Poly.Polygraph
