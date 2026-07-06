import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement

/-! # SaturatedMatchingRenameComponent — the COMPONENT-level Godement renaming relation

`SaturatedMatchingGodement` ships the matching Godement soundness residual reduced to a renaming
witness, but its `MatchingRenameRel` carries a ROOT-level `rootComm`
(`unionFindRootOf t (sigma x) = sigma (unionFindRootOf s x)`) — and the file records that this is
REFUTED (`not_matchingGodementSwapRenameable`, even the fresh variant): `unionFindJoin` roots are
JOIN-ORDER dependent, so transposing the two Godement blocks flips which surviving open wire ends
up the merged component's root.  The docstring names the fix: a COMPONENT-level `rootComm` (the
renaming preserves the same-component partition, without pinning the exact representative root)
plus freshness.

This brick ships that corrected relation.  `MatchingRenameRelComponent` replaces the root-level
`rootComm` with `sameComponentComm` — the boundary `==`-of-roots agreement is transported
DIRECTLY, not through a per-node root commutation.  This is exactly the connectivity view that the
already-shipped `extractDiagram_eq_of_connectivityView` consumes (it reads `matchingSameComponent`,
a `==` of two roots — NOT the roots themselves), so the partition-VIEW half re-closes for the
corrected relation without ever asserting the refuted per-root identity.

  * `MatchingRenameRelComponent` — the component-level renaming relation (equal open-wire / loop
    counts, an injective boundary-fixing node renaming, and same-component preservation on the
    boundary roots);
  * ★ `extractDiagram_of_matchingRenameRelComponent` — component-level renaming-related matching
    states extract to the SAME `DiagramType`, feeding `extractDiagram_eq_of_connectivityView`
    with `sameComponentComm` after re-indexing the boundary nodes through `sigma` via `bnodeCorr`.

The corrected `sameComponentComm` is the field a genuine fresh-id reordering bijection CAN satisfy
(the reordering preserves the partition even when it flips roots), so this unblocks the Godement
soundness sigma the root-level statement made unprovable.  The matching twin of the arc route's
partition-view invariance, at the component level.

Raw Lean 4 + Init; structural mirror of `extractDiagram_of_matchingRenameRel`; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The component-level matching renaming relation.**  `secondState` is a `sigma`-renaming of
`firstState` fixing the bottom boundary — equal open-wire / loop counts, `sigma` injective, every
in-range boundary node of `secondState` the `sigma`-image of the corresponding one of
`firstState` — where the connectivity is transported at the PARTITION level: two boundary roots
of `secondState` at `sigma`-images agree (`==`) exactly when the corresponding `firstState` roots
agree.  This is the CORRECTED form of `MatchingRenameRel`, whose root-level `rootComm` the Godement
transposition refutes (`not_matchingGodementSwapRenameable`): the join-order flips the merged root,
but never the same-component partition, so `sameComponentComm` holds where `rootComm` cannot. -/
structure MatchingRenameRelComponent (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState) : Prop where
  /-- The open-wire counts agree. -/
  lengthEq : secondState.openWires.length = firstState.openWires.length
  /-- The loop counts agree. -/
  loopsEq : secondState.loops = firstState.loops
  /-- The renaming is injective. -/
  inj : ∀ firstNode secondNode, sigma firstNode = sigma secondNode → firstNode = secondNode
  /-- Every in-range boundary node of `secondState` is the `sigma`-image of the corresponding one
  of `firstState`. -/
  bnodeCorr : ∀ index, index < bottomCount + firstState.openWires.length →
      natListGetAt (matchingBoundaryNodes bottomCount secondState) index
        = sigma (natListGetAt (matchingBoundaryNodes bottomCount firstState) index)
  /-- The renaming preserves the same-component partition on the boundary roots (the corrected,
  join-order-robust replacement for the refuted root-level `rootComm`). -/
  sameComponentComm : ∀ firstNode secondNode,
      (unionFindRootOf secondState.links (sigma firstNode)
          == unionFindRootOf secondState.links (sigma secondNode))
        = (unionFindRootOf firstState.links firstNode
          == unionFindRootOf firstState.links secondNode)

/-- ★ **Component-level renaming-invariance of the matching extract.**  Component-level
renaming-related matching states extract to the SAME `DiagramType`: the open-wire / loop counts
come straight from the relation, and the boundary same-component booleans agree because the
boundary nodes correspond under `sigma` (`bnodeCorr`) and `sameComponentComm` transports the
root `==` on the `sigma`-images.  The corrected twin of `extractDiagram_of_matchingRenameRel`
that never touches the refuted per-root identity — it feeds the connectivity view directly. -/
theorem extractDiagram_of_matchingRenameRelComponent (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState)
    (rel : MatchingRenameRelComponent bottomCount sigma firstState secondState) :
    extractDiagram bottomCount firstState = extractDiagram bottomCount secondState := by
  apply extractDiagram_eq_of_connectivityView bottomCount firstState secondState
    rel.lengthEq.symm rel.loopsEq.symm
  intro firstIndex secondIndex firstBelow secondBelow
  show (unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        == unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex))
     = (unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        == unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex))
  rw [rel.bnodeCorr firstIndex firstBelow, rel.bnodeCorr secondIndex secondBelow]
  exact (rel.sameComponentComm _ _).symm

/-! ## Honesty marker -/

/-- **Honesty marker — the COMPONENT-level Godement renaming relation is SHIPPED, and its extract
invariance re-closes the partition view WITHOUT the refuted per-root identity.**
`MatchingRenameRelComponent` replaces `MatchingRenameRel`'s root-level `rootComm` (refuted by the
join-order-dependent `unionFindJoin` roots — `not_matchingGodementSwapRenameable`) with
`sameComponentComm`, the same-component preservation a genuine fresh-id reordering bijection CAN
satisfy; `extractDiagram_of_matchingRenameRelComponent` proves component-level renaming-related
states share a `DiagramType` via `extractDiagram_eq_of_connectivityView`.  What this marker does
NOT claim: CONSTRUCTING the sigma witness between the two Godement run orders (the corrected,
freshness-conditioned `MatchingGodementSwapRenameable` — still the live soundness residual) nor
the completeness `convOfMapEq`.  `= true`. -/
def fxMode_hasMatchingRenameRelComponent : Bool := true

end FX1Poly.Polygraph
