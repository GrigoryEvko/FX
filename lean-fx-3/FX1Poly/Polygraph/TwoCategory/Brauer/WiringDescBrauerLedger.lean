import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwistNormalize

/-! # WP-BRAUER terminal — T2 the crossing-only READBACK target + T3 the terminal LEDGER

This file CLOSES the Brauer lane at its honest terminal state.  It adds no new algebra; it records two things:

  * **T2** — the general crossing-only readback target as a named `Prop` (`BrauerCrossingOnlyReadback`) with its
    residual marker `fxBrauer_hasCrossingOnlyReadback := false`.  It carries NO proof: the general statement needs a
    union-find/permutation state invariant that no shipped lemma supplies (honest scoping below).
  * **T3** — the terminal ledger: the complete `fxBrauer_*` marker table, the modulo-wall decomposition of
    completeness (MACHINE-CHECKED as a conjunction of `rfl`s in `fxBrauer_terminalDecomposition`), the wall
    citation, and the literature-grounded bequest.

Raw Lean 4 + Init; no proof obligations beyond `decide`-smoke non-vacuity + `rfl` marker readouts.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## T2 — the general crossing-only readback target (the residual, NO general proof)

A crossing-only word `crossingWord positions` induces the same Brauer diagram as the PERMUTATION DIAGRAM of the
through-strand permutation it realizes (`permuteOfCrossingWord`).  The union-find boundary read-off tracks the
permutation graph.  Both sides COMPUTE (`Brauer/WiringDescStandardForm.lean` validates the alignment on concrete
words: `readback_smoke_{identity_two, single_crossing, double_crossing, three_strand, yangBaxter}`, all `by decide`).

## Honest scope — why this is a residual, and what carries

  * **Carries (all closed, reusable):** the well-formedness scaffolding is done — `crossingWord_length`,
    `permuteOfCrossingWord_length`, `foldlAdjacentSwap_length`, `applyAdjacentSwap_length`,
    `permutationDiagram_shape` (`Brauer/WiringDescStandardForm.lean`).  The target's SHAPE (equal bottom/top counts,
    zero loops) is `rfl` on both sides.
  * **New (the actual gap):** the general `∀`-proof needs a fresh STATE INVARIANT threading union-find connectivity
    through one `stepWiring crossingWiring` step — an induction relating `processBrauer`'s links to
    `permuteOfCrossingWord`'s one-line permutation.  No shipped lemma supplies it.
  * **The ARC-CUP D-series does NOT carry.**  The `pureCupSpine_sort` / `ArcCupSortComplete` (WalkingAdjunction)
    stack is arc/cup-specific — Fuss–Catalan valley-matching chord-shift descent for the cup/cap block — NOT
    permutation-generic.  So T1 (untwist NF), this readback (T2), and the arc-sort (D-series) are three INDEPENDENT
    legs of the walled master. -/

/-- ★ **The general crossing-only readback target** (T2, residual — no general proof).  For every strand count and
every list of adjacent-transposition positions, the crossing word's Brauer diagram equals the permutation diagram
of the through-strand permutation it realizes.  The shipped `readback_smoke_*` witness concrete instances; the
`∀`-general statement is the residual `fxBrauer_hasCrossingOnlyReadback`. -/
def BrauerCrossingOnlyReadback : Prop :=
  ∀ (bottomCount : Nat) (positions : List Nat),
    brauerDiagramOf bottomCount (crossingWord positions)
      = permutationDiagram bottomCount (permuteOfCrossingWord bottomCount positions)

/-- Non-vacuity — the readback target holds at a FRESH instance beyond the shipped smokes: two commuting crossings
on four strands (`s_0 s_2`) realize the permutation `[1, 0, 3, 2]`.  So the general `Prop` is inhabited at real
instances; the residual is a genuine GENERAL-proof gap, not a vacuous statement. -/
theorem brauerCrossingOnlyReadback_instance_fourStrand :
    brauerDiagramOf 4 (crossingWord [0, 2]) = permutationDiagram 4 (permuteOfCrossingWord 4 [0, 2]) := by decide

/-- **Honesty marker — the general crossing-only READBACK is SCOPED but SMOKES-only (T2 residual).**  The target
`BrauerCrossingOnlyReadback` (`brauerDiagramOf n (crossingWord w) = permutationDiagram n (permuteOfCrossingWord n
w)`) is validated on concrete words (`readback_smoke_*`, `Brauer/WiringDescStandardForm.lean`) and at a fresh
four-strand instance (`brauerCrossingOnlyReadback_instance_fourStrand`), and all its well-formedness scaffolding is
closed.  The general `∀`-proof needs a NEW union-find/permutation state invariant (a `stepWiring crossingWiring`
connectivity induction) that no shipped lemma supplies; the arc-cup `pureCupSpine_sort` D-series does NOT carry
(it is cup-specific, not permutation-generic).  A distinct leg of the walled master, `false` honestly.  `= false`. -/
def fxBrauer_hasCrossingOnlyReadback : Bool := false

/-! ## T3 — the TERMINAL LEDGER

### The complete `fxBrauer_*` marker table (harvested live from `Brauer/*.lean`: 72 true / 12 false / 84 total)

| Marker | Val | File · meaning |
|---|---|---|
| hasWiringDescEngine | T | WiringDesc · `stepWiring` union-find engine |
| hasCrossingGenerator | T | WiringDesc · crossing row, no perm extension |
| hasBrauerPresentation | T | WiringDesc · 5-relation value + per-rel soundness |
| hasBrauerUntwistRelations | T | WiringDesc · r3 two Lehrer–Zhang untwist rows |
| **hasBrauerSoundness** | **T** | WiringDesc · GENERAL soundness (relationAgrees closed) |
| **hasBrauerCompleteness** | **F** | WiringDesc · MASTER — straightening NF, not built |
| hasBrauerUntwistWallDissolved | T | Untwist · r2 crossingParity wall dissolved |
| hasSevenRelationConvSoundness | T | Untwist · soundness covers the 7-relation presentation |
| **hasBrauerStraighteningNFResidual** | **F** | Untwist · residual now constructive, no character |
| **hasUntwistNormalization** | **T** | UntwistNormalize · T1 — findUntwistRedex + fold + freeness |
| hasConnectivityCongruenceDecision | T | StandardForm · `BrauerConv` = diagram equality, decidable |
| hasPermutationStandardForm | T | StandardForm · the permutation NF infrastructure |
| hasCrossingWordCoxeterMoves | T | StandardForm · cancel/braid/commute in context |
| **hasCrossingOnlyStraightening** | **T** | StandardForm · MASTER leg STRAIGHTENED — comb fold BREACH r2 |
| **hasFreeBrauerStraighteningNF** | **F** | StandardForm · full free-Brauer NF, not built |
| **hasCrossingOnlyReadback** | **F** | BrauerLedger · T2 — readback SMOKES-only, state-invariant gap |
| hasUntwistAbsorption | T | Straightening |
| hasCrossingWordFreeCoxeterMoves | T | Straightening |
| **hasCrossingStraighteningInsertionResidual** | **F** | Straightening · MASTER leg — WALLED |
| hasBrauerStraighteningGap | T | StraighteningGap · r2 wall (5 rels under-generate) |
| hasCrossingParityInvariant | T | StraighteningGap · Z/2 character (dissolved for 7) |
| hasCanonicalCrossingWordLayer | T | Insertion |
| hasCrossingWordProblemConditionalReduction | T | Insertion |
| hasInsertionCancelMode | T | Insertion |
| hasInRangeInsertionReformulation | T | Insertion |
| hasInsertionExtendMode | T | Insertion |
| hasInsertionCommuteLocalMove | T | Insertion |
| hasInsertionBraidLocalMove | T | Insertion |
| hasDistantSwapKit | T | Insertion |
| hasInsertionCommuteFullMode | T | Insertion |
| **hasCrossingInsertionStepGeneralResidual** | **F** | Insertion · general step residual |
| hasInsertionReflexAndDescentModes | T | Insertion · r9 |
| hasInsertionOuterInductionAssembly | T | Insertion · r9 outer strong induction closed |
| hasBraidAscentCarryAlgebra | T | Insertion · r10 |
| **hasBraidAscentResidual** | **F** | Insertion · r10 sole leaf = braid-ascent residual |
| hasBraidAscentRegimeBReduction | T | Insertion · r11 Regime-B → two decidable facts |
| **hasBraidAscentLeafWalled** | **T** | Insertion · r12 — THE WALL (Regime A definitive) |
| hasBraidAscentCarryCollapse | T | Insertion · r12 `p2_eq_swapSuccSwap` |
| **hasUntwistContextRewrite** | **T** | Insertion · r12 — the T1 PIVOT (length-decreasing kit) |
| hasWiringArcEventsBlockRotateLegs | T | BlockRotate |
| hasStepWiringArcsComponentView | T | ComponentSim |
| hasWiringDescResidualReduction | T | ComponentSim |
| **hasWiringDescBlockSwapWitness** | **F** | ComponentSim |
| hasConnectivityMonotonicity | T | ConnectivityMono |
| hasOffConfinedConverseAtWord | T | ConnectivityOffConfined |
| hasBrauerConvSoundness | T | Conv · `brauerConv_sound` |
| hasBrauerConvContextualInterchange | T | Conv · Godement move |
| hasBrauerWhiskerMove | T | Conv · congruence move |
| hasBrauerSoundnessResidualNamed | T | Conv |
| hasWiringDescCoreSwapBundleModuloOpenMap | T | CoreSwapBundle |
| hasWiringDescCoreSwapTraces | T | CoreSwap |
| hasWiringDescCoreSwapOrderSwap | T | CoreSwap |
| hasSamePositionSpliceSurgery | T | CrossingInvolution |
| hasCrossingInvolutionReconnection | T | CrossingInvolution |
| **hasCrossingInvolutionReconnectionFlipsSoundness** | **F** | CrossingInvolution |
| hasBoundarySubstitution | T | DirectRelationAgrees |
| hasDirectRelationAgreesAssembler | T | DirectRelationAgrees |
| hasDirectBrauerConvBridge | T | DirectRelationAgrees |
| hasCollapseTrioResidualOffRefutedRoute | T | DirectRelationAgrees |
| hasR1R3ResidualIsTwoWordFunctoriality | T | DirectRelationAgrees |
| **hasBrauerSoundnessDirectRouteResidual** | **F** | DirectRelationAgrees |
| hasTwoWordFunctorialityPort | T | Functoriality |
| hasWhiskerFromFunctoriality | T | Functoriality |
| hasFunctorialRelationAgreesFiveOfFive | T | Functoriality |
| hasBrauerSoundnessResidualIsPadShift | T | Functoriality |
| hasDisjointWindowNextFreshCommute | T | Godement |
| hasDisjointWindowConcreteSoundness | T | Godement |
| hasDisjointWindowUnconditionalRefuted | T | Godement |
| **hasWiringDescDisjointWindowFreshProof** | **F** | Godement |
| hasWiringDescJoinEventReification | T | JoinEvents |
| hasWiringDescCoreSwapOpenMap | T | OpenMap |
| hasWiringDescDisjointWindowFreshInRangeProof | T | OpenMap |
| hasWiringDescDisjointWindowFreshResidualNamed | T | OpenMap |
| hasRightPadCongruence | T | PadCongruence |
| hasTwoSidedPadCongruence | T | PadCongruence · KEYSTONE15 |
| hasRelationInArbitraryHorizontalContext | T | PadCongruence |
| hasSecondEndpointJoinConverse | T | PortReconnection |
| hasCrossingPortReconnection | T | PortReconnection |
| hasPortReconnectionAssemblyBridge | T | PortReconnection |
| **hasBrauerSoundnessPortReconnectionResidual** | **F** | PortReconnection |
| hasWiringDescStateFreshStep | T | Reachable |
| hasReachableStateInvariant | T | Reachable |
| hasWiringDescDisjointWindowFreshRefuted | T | Reachable |
| hasWiringDescWindowLocality | T | WindowLocality |

### The decomposition of completeness (the modulo-wall statement, MACHINE-CHECKED in `fxBrauer_terminalDecomposition`)

`fxBrauer_hasBrauerCompleteness = false` decomposes into six honest sub-statuses:

  1. **Soundness TOTAL** — `hasBrauerSoundness = true`, `hasSevenRelationConvSoundness = true`: every convertible
     pair has equal matching, over the SEVEN-relation Lehrer–Zhang presentation.
  2. **Untwist rows free-decidable + diagram-sound** — the two rows ship as data with `decide` witnesses.
  3. **Untwist-NF T1** — `hasUntwistNormalization = true`: `findUntwistRedex` + `untwistNormalize` + hypothesis-free
     convertibility + output redex-freeness, built on the r12 length-decreasing pivot (`hasUntwistContextRewrite`).
  4. **Crossing readback-target scoped, SMOKES-only** — `hasCrossingOnlyReadback = false` (T2): the right normal
     form, validated at instances, general proof is a state-invariant gap.
  5. **S_n crossing block STRAIGHTENED via the comb fold (BREACH r2)** — `hasCrossingOnlyStraightening = true`
     (`crossingWords_equalPerm_conv` in `Brauer/WiringDescStaircaseCanonical.lean`: equal-permutation crossing words
     are `BrauerConvFree7`-convertible, via the recursive-comb staircase + zero-axiom `combCanonicity`).  The
     *insertion* route stays walled — `hasCrossingStraighteningInsertionResidual = false`,
     `hasBraidAscentLeafWalled = true` (Regime A of the braid-ascent leaf) — the comb fold is the alternate route
     that BYPASSES it.
  6. **Full assembly still blocked** ⇒ `hasBrauerCompleteness = false`: the cup/cap connectivity congruence (bare
     `BrauerConv` suffix congruence via `MatchingConnectivityViewSim` through `processBrauer`) is a distinct leg,
     independent of the `S_n` block.

### The wall citation

`fxBrauer_hasBraidAscentLeafWalled` (`Brauer/WiringDescInsertion.lean`): Regime A gives two reduced words of EQUAL
Coxeter length for the same `S_n` element, joined only by variable-count length-preserving Matsumoto/Tits
braid + commute moves; `ell = inversionCount` is FROZEN across the ascent, and no shipped monovariant descends per
step.  Believed TRUE (Lehrer–Zhang Thm 2.6(2) present the category; its hardest small instance
`crossingWords_conv_residualStuckExample` is exhibited convertible) but measure/route-RESISTANT on the shipped move
set — a wall, not an obstruction to truth.

### The bequest — what an independent route would need to BREACH the wall (literature-grounded)

  * **Matsumoto–Tits** (H. Matsumoto, C.R. Acad. Sci. Paris 258 (1964); J. Tits 1969): two reduced words for the
    same `S_n` element are connected by the Artin braid relations ALONE.  A distinguished-active-letter lexicographic
    descent — `(lastMismatchIndex, activeLetterValue, activeSlotDistance)`, of `pureCupSpine_sort` magnitude — would
    give the `Nat`-fuel recursion the wall lacks.  Mathlib's `CoxeterSystem` supplies only the weak exchange
    property, no drop-in fuel recursion.
  * **Delpeuch–Vicary** (*Normalization for planar string diagrams*, LMCS 18(1) 2022, arXiv:1804.07832): exchange
    (interchanger) normalization is strongly normalizing with a linear-time (connected) / quadratic (general)
    equivalence algorithm for PLANAR diagrams — the "interchanger-normalization route".  Their companion
    (arXiv:2105.04237) shows the BRAIDED word problem is unknot-HARD, which is why the polynomial result is planar.
  * **Lehrer–Zhang** (*The Brauer category and invariant theory*, JEMS 17 (2015), arXiv:1207.5889, Thm 2.6): seven
    relations on four generators are COMPLETE for the Brauer category — so the wall is a route gap, not an
    obstruction to truth.  **Graham–Lehrer** (*Cellular algebras*, Invent. math. 123 (1996)): the standard-form
    basis is the involution-permutation triple (cap half-diagram, `S_k` permutation on through-strands, cup
    half-diagram) — the diagrammatic normal form the untwist-NF T1 and the readback T2 target. -/

/-- ★★ **The terminal decomposition of Brauer completeness — MACHINE-CHECKED.**  The sub-statuses of
`fxBrauer_hasBrauerCompleteness = false` read off directly as marker values (each `rfl`): soundness TOTAL
(`hasBrauerSoundness`, `hasSevenRelationConvSoundness`) · untwist-NF T1 SHIPPED (`hasUntwistNormalization`) · the S_n
crossing block STRAIGHTENED via the comb fold (BREACH r2: `hasCrossingOnlyStraightening` now true, backed by
`crossingWords_equalPerm_conv`; the *insertion* route stays walled — `hasBraidAscentLeafWalled` true,
`hasCrossingStraighteningInsertionResidual` false) · the crossing readback SCOPED (`hasCrossingOnlyReadback` false,
T2) · and the master `hasBrauerCompleteness` STILL false (the cup/cap connectivity congruence is a distinct leg).
This is the honest terminal state of the Brauer lane, recorded as a conjunction the kernel checks. -/
theorem fxBrauer_terminalDecomposition :
    fxBrauer_hasBrauerSoundness = true
      ∧ fxBrauer_hasSevenRelationConvSoundness = true
      ∧ fxBrauer_hasUntwistNormalization = true
      ∧ fxBrauer_hasBraidAscentLeafWalled = true
      ∧ fxBrauer_hasCrossingOnlyReadback = false
      ∧ fxBrauer_hasCrossingOnlyStraightening = true
      ∧ fxBrauer_hasCrossingStraighteningInsertionResidual = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Honesty marker — the WP-BRAUER terminal ledger is RECORDED.**  This file documents the terminal state of the
Brauer lane: the complete 84-marker table (72 true / 12 false), the machine-checked completeness decomposition
(`fxBrauer_terminalDecomposition`), the wall citation (`fxBrauer_hasBraidAscentLeafWalled`), and the
literature-grounded bequest (Matsumoto–Tits / Delpeuch–Vicary interchanger normalization / Lehrer–Zhang seven
relations / Graham–Lehrer cellular standard form).  The lane closes at: soundness total, untwist NF shipped (T1),
readback scoped (T2), the `S_n` block walled, full assembly blocked.  `= true`. -/
def fxBrauer_hasTerminalLedger : Bool := true

end FX1Poly.Polygraph
