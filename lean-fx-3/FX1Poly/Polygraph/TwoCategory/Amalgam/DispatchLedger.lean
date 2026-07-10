import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchMap
import FX1Poly.Polygraph.TwoCategory.Amalgam.Modularity
import FX1Poly.Polygraph.TwoCategory.Amalgam.DecisionTransfer

/-! # Polygraph/TwoCategory/Amalgam/DispatchLedger — the WP-AMALG-2 r1 ledger (B4)

The honest r1 ledger for the WAVE-4 dispatch theorem: what each brick SHIPPED (machine-checked zero-axiom), the
SN-non-modularity caveat, and every surviving jam with its EXACT goal and NAMED blocking node.  Pure docstring +
hypothesis-free `Bool` markers, so every declaration is axiom-free.  Edits NOTHING outside `Amalgam/`.

## What the r1 bricks SHIPPED (each machine-checked zero-axiom, gated in the audit twin)

  * **B1 — THE BLOCK FACTORIZATION + DISPATCH MAP** (`DispatchMap.lean`, `fxAmalg_hasBlockDispatchMap = true`).
    The dispatch routing map `blockTags` (per-block component schedule) with soundness; the block-purity of a
    dispatch-map image (`monoBlockDecompose`: a mono-component word is a single block, with the length corollary);
    the dispatch map FIRING on the real monad unit (`dispatchedMonadUnit` at 2-generator index 0); and the
    non-vacuity CONTRAST — a real combined cell's boundary `s·t` routes to TWO blocks
    (`crossPairDomainRouting = [true, false]`), a dispatch-map image's `t·t` to ONE
    (`monadTailWord_singleBlock`).  The 1-cell substrate present and exercised on a genuinely combined cell.

  * **B2 — THE MODULARITY THEOREM (disjoint scope)** (`Modularity.lean`, `fxAmalg_hasModularityDisjointScope =
    true`).  `pushoutConvIffFree_ofEmptyComponents`: over the pushout with EMPTY component laws, the saturated
    convertibility at `SaturatedConvOverPushout` coincides with the FREE `TwoCellConvFull` — the 2-categorical
    instance of Toyama's confluence-modularity for the disjoint union.  Assembled from the UNCONDITIONAL soundness
    lift (`pushoutPreservesConvLeft` / `pushoutPreservesConvRight`) and the empty-law completeness
    (`saturatedConvOverEmptyRows_iff_full` ∘ `saturatedConvOverPushoutRows_empty`).  Concrete at `involution +_M
    monad` (`involutionMonadPushoutConvIffFree`); non-vacuous blockwise lift of a real monad law
    (`modularityRightBlockLift`); the cross-block Godement commutation leg (`modularityCrossBlockCommute`, FREE).

  * **B3 — THE DECISION TRANSFER + the OMEGA-5 handoff** (`DecisionTransfer.lean`, `fxAmalg_hasDecisionTransfer =
    true`, `fxAmalg_hasOmegaFiveCellSideHandoff = true`).  `involutionMonadPushoutDecisionViaModularity`: a TOTAL
    decider for the pushout's saturated convertibility, routing the FREE-7 decision through the B2 biconditional.
    The concrete demonstrator computes BOTH verdicts on the DISPATCH-MAP images
    (`dispatchedFaceSeparatingVerdict = false`, `dispatchedFaceReflexiveVerdict = true`) and on the s-whiskered pair
    through the transfer (`modularityDecisionSeparatingVerdict = false`, `modularityDecisionReflexiveVerdict =
    true`).  The OMEGA-5 cell-side tensor `⊗_k` is packaged as the soundness functor (`omegaFiveTensorComposition`
    + both legs), inhabited — the arrow OMEGA-5 waits on, without the full-decidability wall.

## The SN-non-modularity caveat (recorded, load-bearing)

The modularity we transfer is of the WORD PROBLEM / CONFLUENCE, not of TERMINATION.  Toyama (1987) proved
confluence IS modular for the disjoint union of rewrite systems, but STRONG NORMALIZATION is NOT — his
counterexample (`F(x,x,x) ← F(0,1,x)` over one signature, projection `G(x,y)→x`, `G(x,y)→y` over a disjoint
other; each terminating, the union looping on `F(G(0,1), G(0,1), G(0,1))`) shows SN fails to transfer even across
DISJOINT signatures.  So B2's "modularity" claims nothing about termination.  Concretely, the decision transfer
(B3) never inherits termination modularly: its totality rests on the FREE decision `decideTwoCellConvFull`, whose
termination is proved DIRECTLY at the amalgam level (the class-saturation fuel bound `classSaturationFuel`,
`fxMode_hasUngatedFreeTwoCellDecision = true`), NOT lifted from the components.  The caveat is why the transfer is
routed through the free decision and the empty-law reflection rather than through any component SN.

## The surviving jams (each: EXACT goal + NAMED blocking node — all `false`, all HONEST)

  * **JAM — the FULL plain-`TwoCellConv` dispatch.**  Goal: inhabit `Dispatch.DispatchDecidability` — the combined
    decider at the interface `DecidableTwoCellConvFor` = `Decidable (TwoCellConv …)` (the PLAIN RST-closure of the
    3-cell rewrite, WITHOUT the completed interchange / whisker functoriality).  NAMED node:
    `fxMode_hasConvergentThreeCellSystem = false` (the deferred Gratzer convergence — the total decider for plain
    `TwoCellConv`).  The shipped `decideTwoCellConvFull` decides the strictly LARGER `TwoCellConvFull`, which does
    NOT transfer to plain `TwoCellConv`.  So `fxAmalg_hasDispatchTheorem` is NOT hypothesis-free inhabitable and
    STAYS `false` — the flip is HELD (B3's `fxAmalg_dispatchTheoremStaysWalled`), NOT fabricated.

  * **JAM — the real-law saturated dispatch completeness.**  Goal: inhabit `SaturatedDispatchDecidability` /
    `fxAmalg_hasFullSaturatedPushoutDispatch` for a component contributing GENUINE fireable laws — every pushout
    derivation must project back to per-component derivations (Nelson-Oppen / Baader-Tinelli purification).  NAMED
    node: purification is sound only for word-preserving / left-connected presentations; the monad unit/mult
    WIRE-CREATING generators break the convex-block projection (`fxAmalg_hasFullSaturatedPushoutDispatch = false`,
    `fxAmalg_hasSaturatedDispatchTheorem = false`).  The commutation and soundness are NOT among the walls (both
    ship); the wall is completeness alone.

  * **JAM — the general fireable-law pushout dispatch.**  Goal: `fxAmalg_hasGeneralPushoutDispatch` — a live
    combined `Decidable` when a component contributes genuine laws.  NAMED node: the purification completeness above
    PLUS (historically) the reconstruction reseat — the latter now SHIPS
    (`fxAmalg_hasReconstructionDecoderReseat = true`), so the residual is purification alone.

  * **JAM — the LEFT real coprojection (n-ary fold with real left 2-generators).**  Goal: fold a THREE-way empty-law
    amalgam whose LEFT component carries real 2-generators (e.g. `(involution +_M monad) +_M monad`).  NAMED node:
    `inclusionLeftTwoReal` does NOT exist — only the RIGHT real coprojection `inclusionRightTwoReal` ships
    (`RealCoprojection.lean`); the vacuous `inclusionLeftTwo` needs a locally-thin left component.  The n-ary fold
    is therefore r1-reachable only with a THIN left factor (`threeWayThinFold`), not with real left 2-generators.

  * **JAM — the pushout universal-property uniqueness.**  Goal: `fxAmalg_hasSignaturePushoutUniqueness` — the hard
    direction of the pushout universal property (the copair is UNIQUE).  NAMED node: `Pushout.lean`
    `fxAmalg_hasSignaturePushoutUniqueness = false`; only the easy direction `copairMorphism` + its restriction
    laws ship.  Orthogonal to the dispatch, recorded for completeness.

## Where OMEGA-5 consumes r1

OMEGA-5's `fxOmega5_enrichedFunctorCellSideReached` jam names `fxAmalg_hasDispatchTheorem` (FULL decidability) as
its blocking node.  B3's finding: the cell-side functor needs only the SOUNDNESS tensor `⊗_k` (`mapCellAlong` +
`mapCellAlong_preservesConvUnconditional`), which SHIPS — so OMEGA-6 can wire `⊗_k` to
`omegaFiveTensorComposition` / `omegaFiveTensorSoundnessLeft` / `omegaFiveTensorSoundnessRight` rather than wait on
the completeness wall.

Raw Lean 4 + Init; a docstring record plus hypothesis-free `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## The r1 shipped-brick marker -/

/-- ★ **The r1 bricks B1–B3 SHIPPED.**  `= true`: the block factorization + dispatch map
(`fxAmalg_hasBlockDispatchMap`), the modularity theorem in the disjoint scope
(`fxAmalg_hasModularityDisjointScope`), and the decision transfer + OMEGA-5 handoff
(`fxAmalg_hasDecisionTransfer`, `fxAmalg_hasOmegaFiveCellSideHandoff`) — each machine-checked zero-axiom. -/
def fxAmalg_r1BricksShipped : Bool := true

/-! ## The SN-non-modularity caveat -/

/-- ★ **The SN-non-modularity caveat is RECORDED.**  `= true`: B2's modularity is of the WORD PROBLEM /
CONFLUENCE (Toyama 1987, modular for the disjoint union), NOT of TERMINATION (Toyama's counterexample — SN is NON-
modular even across disjoint signatures).  The decision transfer's totality rests on the FREE decision's DIRECT
termination (`fxMode_hasUngatedFreeTwoCellDecision`), never on component SN. -/
def fxAmalg_snNonModularCaveat : Bool := true

/-! ## The surviving-jams marker -/

/-- ★ **Every surviving jam is RECORDED with its exact goal + NAMED node.**  `= true`: the full plain-`TwoCellConv`
dispatch (node `fxMode_hasConvergentThreeCellSystem`), the real-law saturated completeness (node
`fxAmalg_hasFullSaturatedPushoutDispatch`, purification for wire-creating generators), the general fireable-law
dispatch (node `fxAmalg_hasGeneralPushoutDispatch`), the LEFT real coprojection (node: `inclusionLeftTwoReal` does
not exist), and the pushout uniqueness (node `fxAmalg_hasSignaturePushoutUniqueness`) — see the file docstring for
each exact goal.  No jam is hidden and none is falsely flipped. -/
def fxAmalg_r1JamsRecorded : Bool := true

/-! ## The ledger marker -/

/-- ★ **The WP-AMALG-2 r1 ledger SHIPS (B4).**  `= true`: per-brick states (B1–B3, each machine-checked
zero-axiom), the SN-non-modularity caveat, and every surviving jam named with its exact goal and NAMED blocking
node.  `fxAmalg_hasDispatchTheorem` is HONESTLY HELD `false` (the plain-`TwoCellConv` interface is the deferred
Gratzer convergence, not the shipped free decision) — no fabricated flip. -/
def fxAmalg_hasDispatchLedger : Bool := true

/-! ## The WP-AMALG-2 r3 section — the reverse-completeness / pushout-NF grind (#2043)

r2 (`RealLawDispatch.lean`) narrowed #2043's wall to reverse-completeness / pushout normal form.  r3 grinds that
wall: it REFUTES the naive NF, gives the CORRECT (gap-indexed) NF with its base-case soundness, lands the
single-gap reverse-completeness leg LIVE off the per-component decider, and writes the `SaturatedOver` sign-off
residual.  #2043 does NOT close — the advance is honest and additive; every held marker is named.

### The r3 bricks SHIPPED (each machine-checked zero-axiom, gated in the audit twin)

  * **B1 — THE s-PREFIX NF REFUTATION** (`SPrefixRefutation.lean`, `fxAmalg_sPrefixNormalFormRefuted = true`).  The
    recon's candidate "commute all involution atoms to a prefix" is machine-checked FALSE.  The exact non-commuting
    word `crossPairTSWord = t·s` factors with the involution block NON-initial (`crossPairTSWord_blockDecompose =
    [(false,[t]),(true,[s])]`), its `s`-to-front reordering `s·t` is a DIFFERENT word (`crossPairTSWord_ne_STWord`,
    so the move is not boundary-preserving), and `t·s` admits NO `s`-prefix split
    (`crossPairTSWord_not_sPrefixForm`) — the free monoid on `{s,t}` does not commute; `crossComponentWhiskerCommute`
    only re-nests DISJOINT whiskers.  A genuine pushout 2-cell realizes the `t·s` boundary
    (`crossPairTSIdentityCell`), so the refutation is non-vacuous.  A refutation is a full deliverable.

  * **B2 — THE GAP-INDEXED NF + BASE-CASE SOUNDNESS** (`PushoutNormalForm.lean`,
    `fxAmalg_pushoutNormalFormGapIndexed = true`).  The correct NF coordinate is gap-indexed — s-walls (fixed
    positions) + per-gap monad content — realized by `pushoutWallBlocks` / `pushoutGapBlocks` computing on the
    witness word `s·t·s·t·t` to two walls `[[s],[s]]` and two gaps `[[t],[t,t]]` (`rfl`).  The BASE-CASE NF
    soundness (single-gap = pure right-image cell converts to its transported monad EZ normal form) SHIPS via
    `pushoutRightImageCompletenessLift` (the shipped unconditional `pushoutPreservesConvRight` specialised to
    `MonadLawRelReconstructed`), non-vacuous on the associativity and left-unit gap collapses
    (`pushoutAssocGapConv` / `pushoutLeftUnitGapConv`).

  * **B3 — THE SINGLE-GAP REVERSE-COMPLETENESS LEG, LIVE** (`ReverseCompletenessLeg.lean`,
    `fxAmalg_hasRightImageReverseCompleteness = true`).  The router `pushoutRightImageDecidesConv` runs the shipped
    TOTAL reconstructed decider `monadReconstructedDecision`; the extractor `pushoutRightImageConvOfDecided`
    transports its positive verdict, via B2's lift, to a pushout convertibility of the right-images.  It FIRES on
    the two associativity foldings and the left-unit law (`_assoc` / `_leftUnit`, `= true`), yields the actual conv
    (`pushoutAssocRightImagesConvViaDecider`), and DECLINES the separating monad faces (`_faces`, `= false`).  The
    per-component decider feeding the pushout, proof-carrying, over the REAL law relation.

  * **B4 — THE SATURATEDOVER SIGN-OFF RESIDUAL** (`SaturatedOver.lean`,
    `fxAmalg_saturatedOverSignOffStaysGated = true`).  The `SaturatedOver → MonadSaturatedConv` deletion pin stays
    GATED on (1) the user erosion decision (retiring `MonadLawRel` / `monadSaturated_iff_generic` voids the
    migration fact), (2) the `DeciderReseat` `MonadWordProblem` import, (3) the `SaturatedRelationFamily.
    monadRelationFamily` member.  r3 does NOT discharge it: the B3 leg runs `monadReconstructedDecision`, which
    still runs the bespoke decider internally, so the bespoke import is not dropped; the migration-iff is
    INDEPENDENT of the dispatch.  r3 only reinforces that step (1)'s erosion is safe.

### The surviving r3 jams (each: EXACT goal + NAMED node — all HONEST, no fabricated flip)

  * **JAM — the multi-gap NF splice.**  Goal: assemble per-gap normal forms across a shared s-wall into one
    boundary NF (the SPLICE lemma: adjacent gap-cells across a wall compose to the gap-EZ of the concatenation).
    NAMED node: `fxAmalg_pushoutNormalFormSpliceStaysWalled` (`PushoutNormalForm.lean`); crux rides the CONSUME-only
    `WalkingMonad/MonadNormalizeVcomp.wordMul_vcomp` + the shipped `crossComponentWhiskerCommute`.

  * **JAM — the isFalse reflection (conservativity).**  Goal: a TWO-SIDED right-image decider needs "pushout
    non-conv of images ⟹ monad non-conv of pre-images" (the Nelson-Oppen / Baader-Tinelli purification for the
    wire-creating generators, OR reconstructed `convOfMapEq` + fold-preservation-under-`mapCellAlong`).  NAMED
    node: `fxAmalg_fullReverseCompletenessStaysWalled` (`ReverseCompletenessLeg.lean`).  The single-gap leg is
    ONE-SIDED (isTrue completeness only).

  * **JAM — the LEFT real coprojection.**  Goal: the left-image fragment with real 2-generators.  NAMED node:
    `inclusionLeftTwoReal` does not exist (the r1 jam, unchanged) — only the thin `inclusionLeftTwo` ships.

  * **HELD (no flip) — the full saturated / general dispatch.**  `fxAmalg_hasFullSaturatedPushoutDispatch`
    (`DispatchSaturated.lean`) STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS
    `false`; `fxAmalg_realLawCompletenessStaysWalled` (`RealLawDispatch.lean`) STAYS `true`.  #2043 remains OPEN. -/

/-- ★ **The r3 bricks B1–B4 SHIPPED.**  `= true`: the s-prefix NF refutation (`fxAmalg_sPrefixNormalFormRefuted`),
the gap-indexed NF + base-case soundness (`fxAmalg_pushoutNormalFormGapIndexed`), the single-gap reverse-
completeness leg LIVE off the per-component decider (`fxAmalg_hasRightImageReverseCompleteness`), and the
`SaturatedOver` sign-off residual (`fxAmalg_saturatedOverSignOffStaysGated`) — each machine-checked zero-axiom. -/
def fxAmalg_r3BricksShipped : Bool := true

/-- ★ **Every surviving r3 jam is RECORDED with its exact goal + NAMED node; #2043 does NOT close.**  `= true`:
the multi-gap NF splice (node `fxAmalg_pushoutNormalFormSpliceStaysWalled`), the isFalse reflection / conservativity
(node `fxAmalg_fullReverseCompletenessStaysWalled`), the LEFT real coprojection (node: `inclusionLeftTwoReal` does
not exist), and the HELD full-dispatch markers (`fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` stay `false`, `fxAmalg_realLawCompletenessStaysWalled` stays `true`) — see the
r3 section docstring for each exact goal.  No jam is hidden and none is falsely flipped. -/
def fxAmalg_r3JamsRecorded : Bool := true

end FX1Poly.Polygraph.Amalgam
