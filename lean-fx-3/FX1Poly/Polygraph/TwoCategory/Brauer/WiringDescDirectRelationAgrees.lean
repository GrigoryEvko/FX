import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPortReconnection
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # KEYSTONE13 — the DIRECT `relationAgrees` assembler, OFF the refuted cross-order route

The shipped whisker-feed `relationAgrees_of_matchingComponentRenameRel` (`Brauer/WiringDescPortReconnection.lean`)
consumes a full `MatchingComponentRenameRel` witness, whose `componentComm` field is a same-component correspondence
over ALL nodes under a `sigma`-renaming.  For the overlapping-window relations R1 (cap-slide) and R3 (Yang-Baxter)
that all-nodes cross-order `componentComm` is the block-swap partition independence whose only known renaming route is
REFUTED (`fxBrauer_hasWiringDescBlockSwapWitness = false`, `Brauer/WiringDescComponentSim.lean`).  Thirteen rounds
pinned the residual to that one supplier.

This file ships a strictly WEAKER, NON-refuted whisker-feed that never mentions `sigma` and never asks for an
all-nodes `componentComm`.  The whisker's `relationAgrees` — a boundary same-component EQUALITY between the two
post-word states — factors through exactly two boundary-restricted facts:

  * **`reconnect` (H1, port-reconnection):** for each in-range boundary index, the LEFT state's boundary node is
    left-connected to the RIGHT state's boundary node at the same index (identity for off-window indices; the window
    reconnection for the window indices).
  * **`boundaryTwoSided` (H2, boundary-restricted two-sided locality):** the RIGHT state's boundary nodes have the
    SAME connectivity read in the LEFT state as in the RIGHT state — a two-sided locality RESTRICTED to the boundary
    probes (NOT an all-nodes / cross-order `componentComm`, NOT a `sigma`-renaming).

Given only H1 + H2, the boundary substitution `isSameComponent_congr` (same-component transitivity: two nodes joined
to a corresponding pair read the corresponding same-component boolean) rewrites the LEFT boundary read to the RIGHT
boundary read, then H2 lands the RIGHT-state read — no cross-order, no renaming.

## What this file SHIPS (each piece zero-axiom, structural)

  * ★ **`isSameComponent_congr`** — the boundary substitution: if `nodeA ~ nodeA'` and `nodeB ~ nodeB'` in `links`,
    then `isSameComponent links nodeA nodeB = isSameComponent links nodeA' nodeB'`.  Pure same-component
    transitivity / symmetry (mirrors the `of_decide_eq_true` / `decide_eq_true` idiom of `isSameComponent_trans`).
  * ★ **`relationAgrees_of_boundaryReconnect_twoSided`** — the DIRECT assembler: `reconnect` (H1) + `boundaryTwoSided`
    (H2) yield the whisker's `relationAgrees` shape, WITHOUT the `MatchingComponentRenameRel` / cross-order route.
  * ★ **`brauerConv_of_boundaryReconnect_twoSided`** — feeds H1 + H2 + the length / loop agreement into the shipped
    `whisker` move, yielding a full contextual `BrauerConv` off the refuted route.
  * ★ **`brauerConv_whisker_crossingInvolution_direct`** — NON-VACUITY: R2 whiskered at offset `1` after a prefix
    crossing, the SAME contextual convertibility the shipped concrete case gives, but assembled through H1 + H2
    (each discharged by `decide`), proving the direct route is genuinely inhabited and correct.

## Honest scope — this does NOT flip `fxBrauer_hasBrauerSoundness`; it RE-POINTS the residual off the refutation

The uniform (all reachable states / offsets) H1 and H2 are NOT discharged this round for any relation.  But this
assembler PROVES the residual for the COLLAPSE TRIO (snake / snakeMirror / R2, whose `rhs = []`) is EXACTLY H1
(port-reconnection surgery mapping the window boundary index to its reconnected node) + H2 (boundary-restricted
two-sided locality, the collapse word being a net-identity on the old boundary partition) — BOTH non-refuted,
provable-in-principle without the block-swap cross-order.  So the collapse trio is NOT blocked by the refutation.
For the overlapping-window R1 / R3 (both sides non-empty, distinct words) the boundary reads of the two sides land on
DIFFERENT fresh realizations of a permutation, so H1 + H2 as stated between the two words is the two-word
functoriality / compositionality bridge (the crossing-free spine's `processSpine_extract_eq_ofCanonicalExtractEq`
ported to `processBrauer`, ~3-4 read-off bricks) — also non-refuted (Selinger, arXiv:0908.3347, Thm 3.12 / 4.33: a
symmetric / compact-closed equation holds iff the diagrams are isomorphic, i.e. equal matching + loops), NOT the
block-swap the refutation kills.  `fxBrauer_hasBrauerSoundness` STAYS `false`; the residual is re-pointed, sharpened,
and confirmed off the refuted cross-order.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The boundary substitution lemma -/

/-- ★ **Same-component boundary substitution.**  If `nodeA` shares a component with `nodeA'` and `nodeB` with
`nodeB'`, then the two nodes' same-component boolean equals the corresponding pair's — pure transitivity /
symmetry of the same-component relation (the `of_decide_eq_true` / `decide_eq_true` idiom of `isSameComponent_trans`
over `unionFindRootOf` equalities).  This is the workhorse that lets a boundary read at the LEFT state's window node
be replaced by the read at the RIGHT state's window node once the two are known to reconnect. -/
theorem isSameComponent_congr (links : List (Nat × Nat)) (nodeA nodeA' nodeB nodeB' : Nat)
    (reconnFirst : isSameComponent links nodeA nodeA' = true)
    (reconnSecond : isSameComponent links nodeB nodeB' = true) :
    isSameComponent links nodeA nodeB = isSameComponent links nodeA' nodeB' := by
  cases hright : isSameComponent links nodeA' nodeB' with
  | true =>
      exact isSameComponent_trans links nodeA nodeB' nodeB
        (isSameComponent_trans links nodeA nodeA' nodeB' reconnFirst hright)
        (isSameComponent_flip links nodeB nodeB' reconnSecond)
  | false =>
      cases hleft : isSameComponent links nodeA nodeB with
      | true =>
          exact absurd
            (isSameComponent_trans links nodeA' nodeB nodeB'
              (isSameComponent_trans links nodeA' nodeA nodeB
                (isSameComponent_flip links nodeA nodeA' reconnFirst) hleft)
              reconnSecond)
            (by rw [hright]; exact fun contra => Bool.noConfusion contra)
      | false => rfl

/-! ## The direct assembler -/

/-- ★ **The DIRECT `relationAgrees`, off the refuted cross-order route.**  The whisker's boundary same-component
equality between two states follows from two boundary-restricted facts, with NO `sigma`-renaming and NO all-nodes
`componentComm`:

  * `reconnect` (H1): the LEFT state's boundary node at each in-range index reconnects (in the LEFT links) to the
    RIGHT state's boundary node at the same index;
  * `boundaryTwoSided` (H2): the RIGHT state's boundary nodes read the same connectivity in the LEFT links as in the
    RIGHT links.

The boundary substitution `isSameComponent_congr` (via H1) rewrites the LEFT boundary read to the RIGHT boundary
read; H2 lands the RIGHT-state read.  `matchingSameComponent` is definitionally the `unionFindRootOf`-`==` these
manipulate, so the `show` bridges the two forms. -/
theorem relationAgrees_of_boundaryReconnect_twoSided (bottomCount : Nat)
    (firstState secondState : WireState)
    (reconnect : ∀ index,
        index < bottomCount + firstState.openWires.length →
        isSameComponent firstState.links
            (natListGetAt (matchingBoundaryNodes bottomCount firstState) index)
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) index) = true)
    (boundaryTwoSided : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        isSameComponent firstState.links
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex)
          = isSameComponent secondState.links
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex)) :
    ∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        matchingSameComponent bottomCount firstState firstIndex secondIndex
          = matchingSameComponent bottomCount secondState firstIndex secondIndex := by
  intro firstIndex secondIndex firstBelow secondBelow
  show isSameComponent firstState.links
        (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex)
      = isSameComponent secondState.links
        (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex)
  exact (isSameComponent_congr firstState.links
        (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex)
        (reconnect firstIndex firstBelow) (reconnect secondIndex secondBelow)).trans
      (boundaryTwoSided firstIndex secondIndex firstBelow secondBelow)

/-- ★ **A boundary-reconnection + boundary-two-sided pair flips into a contextual `BrauerConv`.**  Feeds the shipped
`whisker` move: `lengthsAgree` / `loopsAgree` are the open-wire / loop agreements, and `relationAgrees` comes from
`relationAgrees_of_boundaryReconnect_twoSided`.  This is the direct-route analog of
`brauerConv_of_matchingComponentRenameRel`, but its two premises are the NON-refuted boundary-restricted facts (H1
port-reconnection + H2 boundary two-sided locality), not a full `MatchingComponentRenameRel` with its all-nodes
cross-order `componentComm`. -/
theorem brauerConv_of_boundaryReconnect_twoSided (bottomCount : Nat)
    (prefixAtoms wordLeft wordRight : List BrauerAtom)
    (lengthsAgree :
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length
          = (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight).openWires.length)
    (loopsAgree :
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).loops
          = (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight).loops)
    (reconnect : ∀ index,
        index < bottomCount
            + (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length →
        isSameComponent (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).links
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft)) index)
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) index) = true)
    (boundaryTwoSided : ∀ firstIndex secondIndex,
        firstIndex < bottomCount
            + (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length →
        secondIndex < bottomCount
            + (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length →
        isSameComponent (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).links
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) firstIndex)
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) secondIndex)
          = isSameComponent (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight).links
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) firstIndex)
            (natListGetAt (matchingBoundaryNodes bottomCount
                (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) secondIndex)) :
    BrauerConv bottomCount (prefixAtoms ++ wordLeft) (prefixAtoms ++ wordRight) :=
  BrauerConv.whisker bottomCount prefixAtoms wordLeft wordRight lengthsAgree loopsAgree
    (relationAgrees_of_boundaryReconnect_twoSided bottomCount
      (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft)
      (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)
      reconnect boundaryTwoSided)

/-! ## Non-vacuity — R2 whiskered in context, assembled through the DIRECT route

The concrete post-prefix states for the crossing-involution relation R2 fired at offset `1` after a prefix crossing.
Its two boundary-restricted premises are `decide`-discharged in the `Nat.decidableBallLT`-friendly order (guard
immediately after each binder). -/

/-- H1 (port-reconnection) for R2-at-offset-1 after a prefix crossing: each in-range boundary node of the fired
state reconnects to the corresponding boundary node of the unfired (prefix) state.  `decide`. -/
private theorem directCrossingInvolution_reconnect_ordered : ∀ index,
    index < 3
        + (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1]).openWires.length →
    isSameComponent (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1]).links
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1])) index)
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom))) index)
      = true := by decide

/-- H2 (boundary-restricted two-sided locality) for R2-at-offset-1 after a prefix crossing: the prefix-state boundary
nodes read the same connectivity in the fired links as in the prefix links.  `decide`. -/
private theorem directCrossingInvolution_twoSided_ordered : ∀ firstIndex,
    firstIndex < 3
        + (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1]).openWires.length →
    ∀ secondIndex,
    secondIndex < 3
        + (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1]).openWires.length →
    isSameComponent (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) [crossingAt 1, crossingAt 1]).links
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom))) firstIndex)
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom))) secondIndex)
      = isSameComponent (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom)).links
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom))) firstIndex)
        (natListGetAt (matchingBoundaryNodes 3
            (processBrauer (processBrauer (brauerSeed 3) [crossingAt 0]) ([] : List BrauerAtom))) secondIndex)
      := by decide

/-- ★ **The DIRECT route is NON-VACUOUS.**  R2 (crossing involutivity) fired at offset `1` after a prefix crossing on
strands `0,1` is convertible to the identity — the SAME contextual convertibility the shipped concrete case
(`brauerConv_whisker_crossingInvolution_inContext`) gives, but here ASSEMBLED through the direct route: the two
boundary-restricted premises (H1 port-reconnection, H2 boundary two-sided locality) are `decide`-discharged and fed
to `brauerConv_of_boundaryReconnect_twoSided`.  No `MatchingComponentRenameRel`, no `sigma`, no cross-order. -/
theorem brauerConv_whisker_crossingInvolution_direct :
    BrauerConv 3 ([crossingAt 0] ++ [crossingAt 1, crossingAt 1]) ([crossingAt 0] ++ ([] : List BrauerAtom)) :=
  brauerConv_of_boundaryReconnect_twoSided 3 [crossingAt 0] [crossingAt 1, crossingAt 1] []
    (by decide) (by decide)
    (fun index hindex => directCrossingInvolution_reconnect_ordered index hindex)
    (fun firstIndex secondIndex hfirst hsecond =>
      directCrossingInvolution_twoSided_ordered firstIndex hfirst secondIndex hsecond)

/-! ## Honesty markers -/

/-- **Honesty marker — the same-component boundary substitution is SHIPPED.**  `isSameComponent_congr` transports a
same-component boolean across a reconnection of both probes (pure transitivity / symmetry).  `= true`. -/
def fxBrauer_hasBoundarySubstitution : Bool := true

/-- ★ **Honesty marker — the DIRECT `relationAgrees` assembler is SHIPPED, OFF the refuted cross-order route.**
`relationAgrees_of_boundaryReconnect_twoSided` produces the whisker's boundary same-component equality from two
boundary-restricted premises — `reconnect` (H1 port-reconnection at the boundary indices) and `boundaryTwoSided`
(H2 boundary-restricted two-sided locality) — with NO `sigma`-renaming and NO all-nodes `componentComm`.  It is
strictly WEAKER than the shipped `relationAgrees_of_matchingComponentRenameRel` (which needs a full
`MatchingComponentRenameRel`), and crucially it never invokes the block-swap partition independence
(`fxBrauer_hasWiringDescBlockSwapWitness = false`) that thirteen rounds pinned the residual to.  `= true`. -/
def fxBrauer_hasDirectRelationAgreesAssembler : Bool := true

/-- ★ **Honesty marker — the DIRECT-route `BrauerConv` bridge is SHIPPED and NON-VACUOUS.**
`brauerConv_of_boundaryReconnect_twoSided` feeds H1 + H2 + length / loop agreement into the shipped `whisker` move;
`brauerConv_whisker_crossingInvolution_direct` exhibits R2 whiskered at offset `1` after a prefix crossing — the SAME
contextual convertibility as the shipped concrete case, but assembled through the direct route (H1 / H2 each
`decide`-discharged), proving the assembler is genuinely inhabited and correct.  `= true`. -/
def fxBrauer_hasDirectBrauerConvBridge : Bool := true

/-- ★ **Honesty marker — the COLLAPSE TRIO residual is RE-POINTED off the refutation.**  For snake / snakeMirror / R2
(all `rhs = []`, so the right state is the prefix state), the direct assembler proves `relationAgrees` reduces to
EXACTLY H1 (the collapse word's window boundary indices reconnect to their original strands — port-reconnection
surgery over the shipped `stepWiring_crossing_reconnects` at arbitrary offset) + H2 (the collapse word is a
net-identity on the old boundary partition — boundary-restricted two-sided locality, the monotone half
`processBrauer_isSameComponent_ofBase` plus a per-word old-endpoint confinement).  BOTH are non-refuted and
provable-in-principle WITHOUT the block-swap cross-order.  So the collapse trio is NOT blocked by the refutation; its
uniform (all reachable states / offsets) H1 + H2 is the remaining, non-refuted, real work.  `= true`. -/
def fxBrauer_hasCollapseTrioResidualOffRefutedRoute : Bool := true

/-- ★ **Honesty marker — R1 / R3's residual is the two-word FUNCTORIALITY bridge, NOT the refuted block-swap.**  For
the overlapping-window R1 (cap-slide) and R3 (Yang-Baxter) both sides are non-empty distinct words, so the two
boundary reads land on DIFFERENT fresh realizations of the same permutation; H1 + H2 between the two words is then the
compositionality / functoriality bridge (the crossing-free spine's `processSpine_extract_eq_ofCanonicalExtractEq`
ported to `processBrauer` — an unbuilt ~3-4 read-off brick port), which is ALSO non-refuted (Selinger,
arXiv:0908.3347, Thm 3.12 / 4.33: a symmetric / compact-closed equation holds iff the diagrams are isomorphic, i.e.
equal boundary matching + loops) and independent of the block-swap the refutation kills.  The refutation is confined
to that ONE supplier and does not genuinely wall R1 / R3.  `= true`. -/
def fxBrauer_hasR1R3ResidualIsTwoWordFunctoriality : Bool := true

/-- **Honesty marker — `fxBrauer_hasBrauerSoundness` STAYS `false`; the direct route discharges 0/5 uniform
`relationAgrees` this round.**  The DIRECT assembler re-points the residual off the refuted cross-order onto the
non-refuted boundary-restricted facts (H1 port-reconnection + H2 boundary two-sided locality), and closes them
CONCRETELY for R2-at-offset-1 (`brauerConv_whisker_crossingInvolution_direct`); the UNIFORM (all reachable states /
offsets) H1 + H2 remain unbuilt — the collapse trio needs the port-reconnection surgery + per-word old-endpoint
confinement, R1 / R3 need the spine-to-Brauer functoriality port.  No relation's uniform `relationAgrees` closes, so
`fxBrauer_hasBrauerSoundness` stays `false`; but the WALL is decisively re-attributed: it is NOT the block-swap
refutation, it is the unbuilt (non-refuted) H1 + H2.  `= false`. -/
def fxBrauer_hasBrauerSoundnessDirectRouteResidual : Bool := false

end FX1Poly.Polygraph
