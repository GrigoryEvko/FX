import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim

/-! # KEYSTONE2 — the generic-`WiringDesc` COMPONENT substrate + the sharpened residual reduction

The disjoint-window residual `WiringDescDisjointWindowFresh` (`Brauer/WiringDescGodement.lean`) reduces — through
the engine-agnostic read-off `extractDiagram_of_matchingComponentRenameRel` (`FreeTwoCell/MatchingComponentSim`)
— to constructing a `MatchingComponentRenameRel` between the two window-disjoint firing orders, with
`sigma = blockRotate state.nextFresh descA.outputCount descB.outputCount` (the two fresh output blocks rotated).
Its four fields split into a SAME-ORDER renaming half (open-wire locality + the arc-fold partition transport) and
an ORDER-SWAP half (the join-order independence of the union-find partition).

## What this file SHIPS (each piece zero-axiom, over the GENERIC `stepWiring` engine, crossing included)

  * ★ **`wiringEndpointNode_map`** — decoding a wiring endpoint tag through `sigma`-relabeled input / output node
    lists commutes with `sigma` (both `natListGetAt` branches, needs only `sigma 0 = 0`).
  * ★ **`isUnionFindForest_stepWiringArcs`** — the generic arc fold preserves the union-find forest invariant (the
    fold only ever `unionFindJoin`s or leaves links untouched; `isUnionFindForest_unionFindJoin` per join step).
  * ★ **`stepWiringArcs_componentView`** — the GENERIC ARC FOLD `componentComm`, the reusable half the adjunction
    kit never built.  The component (same-component-boolean) view transports through the WHOLE arc list under a
    `sigma`-relabeling of the endpoint node lists — the fold-lifting of the shipped single-join workhorse
    `componentView_unionFindJoin`, with the loop-vs-join branch agreeing on both sides (the branch test transports
    by the carried component correspondence) so the loop counts also agree.  NO injectivity, NO freshness, NO
    root-level commutation.
  * ★ **`stepWiring_links_isUnionFindForest`** — one `stepWiring` step preserves the forest invariant.
  * ★ **`wiringDescDisjointWindowFresh_of_componentRenameRel`** — the SHARPENED residual reduction: the general
    disjoint-window extract commutation follows from a block-swap `MatchingComponentRenameRel` witness at every
    fresh, disjoint-window configuration.  This pins the residual to EXACTLY the witness (`sigma = blockRotate`,
    its `bnodeCorr` open-wire locality, `componentComm` join-order independence, `loopsEq` cyclomatic invariance).

## The residual that remains (NOT discharged)

The block-swap `MatchingComponentRenameRel` witness itself — the ORDER-SWAP `componentComm`: that folding
`descA`'s arcs then `descB`'s versus `descB`'s then `descA`'s reaches `sigma`-corresponding union-find PARTITIONS.
That is the join-order independence of the union-find closure, the SAME standing open witness the adjunction
keystone rides (`fxMode_hasMatchingComponentCoreSwapWitness = false`, `MatchingGodementComponentCoreSwap`) — now
confirmed shared with the generic engine.  `stepWiringArcs_componentView` closes the SAME-ORDER relabeling leg of
it; the cross-order leg is open.  So `fxBrauer_hasWiringDescDisjointWindowFreshProof` and
`fxBrauer_hasBrauerSoundness` stay `false`.

Raw Lean 4 + Init; reuses the shipped `WireState` / union-find primitives verbatim.  Structural recursion, no
`omega` / `simp`-AC / `native_decide`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Decoding through a renamed node list -/

/-- ★ **Decoding a wiring endpoint tag through `sigma`-relabeled node lists commutes with `sigma`.**  Both
branches of `wiringEndpointNode` are a `natListGetAt` on a relabeled list, which pushes `sigma` out
(`natListGetAt_map`, needing only `sigma 0 = 0` for the past-end default). -/
theorem wiringEndpointNode_map (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (inputNodes outputNodes : List Nat) (inputCount tag : Nat) :
    wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount tag
      = sigma (wiringEndpointNode inputNodes outputNodes inputCount tag) := by
  show (if tag < inputCount then natListGetAt (inputNodes.map sigma) tag
          else natListGetAt (outputNodes.map sigma) (tag - inputCount))
      = sigma (if tag < inputCount then natListGetAt inputNodes tag
          else natListGetAt outputNodes (tag - inputCount))
  split <;> rw [natListGetAt_map sigma sigmaFixesZero]

/-! ## The generic arc fold preserves the union-find forest -/

/-- ★ **The generic arc fold preserves the forest invariant.**  `stepWiringArcs` either leaves `links` untouched
(the loop branch) or `unionFindJoin`s two nodes (the join branch, forest-preserving by
`isUnionFindForest_unionFindJoin`); structural on the arc list. -/
theorem isUnionFindForest_stepWiringArcs (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    isUnionFindForest links →
    isUnionFindForest (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).fst
  | [], _, links, forest => forest
  | (firstTag, secondTag) :: rest, loopsAcc, links, forest => by
      show isUnionFindForest
          (stepWiringArcs inputNodes outputNodes inputCount ((firstTag, secondTag) :: rest) loopsAcc links).fst
      dsimp only [stepWiringArcs]
      split
      · exact isUnionFindForest_stepWiringArcs inputNodes outputNodes inputCount rest (loopsAcc + 1) links forest
      · exact isUnionFindForest_stepWiringArcs inputNodes outputNodes inputCount rest loopsAcc
          (unionFindJoin links
            (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
            (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
          (isUnionFindForest_unionFindJoin links _ _ forest)

/-! ## The generic arc fold `componentComm` — the same-order relabeling leg -/

/-- ★ **The component view transports through the WHOLE arc fold under a `sigma`-relabeling.**  Given the input
correspondence `comp` on the incoming links, folding the SAME arc list over the source nodes and over their
`sigma`-images keeps the same-component booleans corresponding (`componentView_unionFindJoin` per join step, the
branch test agreeing by `comp` at the two decoded endpoints so both fold identically) and yields equal loop
counts.  The reusable fold-lifting of the single-join workhorse — the generic-engine analog of the adjunction
kit's per-step `componentComm`, over ARBITRARY arcs (crossing included), no injectivity / freshness. -/
theorem stepWiringArcs_componentView (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (linksS linksT : List (Nat × Nat)) →
    isUnionFindForest linksS → isUnionFindForest linksT →
    (∀ a b, (unionFindRootOf linksT (sigma a) == unionFindRootOf linksT (sigma b))
        = (unionFindRootOf linksS a == unionFindRootOf linksS b)) →
    (∀ a b,
        (unionFindRootOf
              (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount arcs loopsAcc linksT).fst
              (sigma a)
          == unionFindRootOf
              (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount arcs loopsAcc linksT).fst
              (sigma b))
        = (unionFindRootOf (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc linksS).fst a
          == unionFindRootOf (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc linksS).fst b))
      ∧ (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc linksS).snd
          = (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount arcs loopsAcc linksT).snd
  | [], _, _, _, _, _, comp => ⟨comp, rfl⟩
  | (firstTag, secondTag) :: rest, loopsAcc, linksS, linksT, forestS, forestT, comp => by
      -- the two decoded endpoints, source side
      have firstDecodeT : wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount firstTag
          = sigma (wiringEndpointNode inputNodes outputNodes inputCount firstTag) :=
        wiringEndpointNode_map sigma sigmaFixesZero inputNodes outputNodes inputCount firstTag
      have secondDecodeT : wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount secondTag
          = sigma (wiringEndpointNode inputNodes outputNodes inputCount secondTag) :=
        wiringEndpointNode_map sigma sigmaFixesZero inputNodes outputNodes inputCount secondTag
      -- the branch test agrees on the two sides (stated in the sigma-form the decode rewrites produce)
      have testEq : isSameComponent linksT
              (sigma (wiringEndpointNode inputNodes outputNodes inputCount firstTag))
              (sigma (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
          = isSameComponent linksS
              (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag) :=
        comp (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
          (wiringEndpointNode inputNodes outputNodes inputCount secondTag)
      -- reduce one fold step on both sides
      show (∀ a b,
            (unionFindRootOf
                (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount
                  ((firstTag, secondTag) :: rest) loopsAcc linksT).fst (sigma a)
              == unionFindRootOf
                (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount
                  ((firstTag, secondTag) :: rest) loopsAcc linksT).fst (sigma b))
            = (unionFindRootOf (stepWiringArcs inputNodes outputNodes inputCount
                  ((firstTag, secondTag) :: rest) loopsAcc linksS).fst a
              == unionFindRootOf (stepWiringArcs inputNodes outputNodes inputCount
                  ((firstTag, secondTag) :: rest) loopsAcc linksS).fst b))
        ∧ (stepWiringArcs inputNodes outputNodes inputCount ((firstTag, secondTag) :: rest) loopsAcc linksS).snd
            = (stepWiringArcs (inputNodes.map sigma) (outputNodes.map sigma) inputCount
                ((firstTag, secondTag) :: rest) loopsAcc linksT).snd
      dsimp only [stepWiringArcs]
      rw [firstDecodeT, secondDecodeT, testEq]
      cases hbranch :
          isSameComponent linksS (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
            (wiringEndpointNode inputNodes outputNodes inputCount secondTag) with
      | true =>
          exact stepWiringArcs_componentView sigma sigmaFixesZero inputNodes outputNodes inputCount rest
            (loopsAcc + 1) linksS linksT forestS forestT comp
      | false =>
          exact stepWiringArcs_componentView sigma sigmaFixesZero inputNodes outputNodes inputCount rest
            loopsAcc
            (unionFindJoin linksS (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            (unionFindJoin linksT (sigma (wiringEndpointNode inputNodes outputNodes inputCount firstTag))
              (sigma (wiringEndpointNode inputNodes outputNodes inputCount secondTag)))
            (isUnionFindForest_unionFindJoin linksS _ _ forestS)
            (isUnionFindForest_unionFindJoin linksT _ _ forestT)
            (componentView_unionFindJoin sigma linksS linksT forestS forestT
              (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag) comp)

/-! ## One `stepWiring` step preserves the forest -/

/-- ★ **One `stepWiring` step preserves the forest invariant** — its links are the generic arc fold's output over
the incoming (forest) links, forest-stable by `isUnionFindForest_stepWiringArcs`. -/
theorem stepWiring_links_isUnionFindForest (state : WireState) (position : Nat) (desc : WiringDesc)
    (forest : isUnionFindForest state.links) :
    isUnionFindForest (stepWiring state position desc).links :=
  isUnionFindForest_stepWiringArcs
    (natListSliceAt state.openWires position desc.inputCount)
    ((List.range desc.outputCount).map (· + state.nextFresh))
    desc.inputCount desc.arcs 0 state.links forest

/-! ## The sharpened residual reduction -/

/-- ★ **The disjoint-window residual reduces to a block-swap `MatchingComponentRenameRel` witness.**  Given, at
every fresh disjoint-window configuration, a renaming `sigma` (the intended `blockRotate state.nextFresh
descA.outputCount descB.outputCount`) making the two firing orders `MatchingComponentRenameRel`-related, the
extract commutes — directly through the engine-agnostic read-off `extractDiagram_of_matchingComponentRenameRel`.
This pins `WiringDescDisjointWindowFresh` to EXACTLY the witness's four fields: `lengthEq` (disjoint-window
open-wire locality), `bnodeCorr` (the `blockRotate` boundary correspondence), `componentComm` (the join-order
independence of the union-find partition — the standing open leg, same as `MatchingGodementComponentCoreSwap`),
and `loopsEq` (cyclomatic invariance).  `stepWiringArcs_componentView` closes the SAME-ORDER relabeling leg of
`componentComm`; the cross-order leg is open. -/
theorem wiringDescDisjointWindowFresh_of_componentRenameRel
    (witness : ∀ (state : WireState) (positionA positionB bottomCount : Nat) (descA descB : WiringDesc),
        WiringDescStateFresh state → bottomCount ≤ state.nextFresh →
        positionA + descA.inputCount ≤ positionB →
        ∃ sigma : Nat → Nat, MatchingComponentRenameRel bottomCount sigma
          (stepWiring (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB)
          (stepWiring (stepWiring state positionB descB) positionA descA)) :
    WiringDescDisjointWindowFresh := by
  intro state positionA positionB bottomCount descA descB fresh bottomBound disjoint
  obtain ⟨sigma, rel⟩ :=
    witness state positionA positionB bottomCount descA descB fresh bottomBound disjoint
  exact extractDiagram_of_matchingComponentRenameRel bottomCount sigma _ _ rel

/-! ## Honesty markers -/

/-- **Honesty marker — the generic arc fold `componentComm` is SHIPPED.**  `stepWiringArcs_componentView` lifts
the single-join workhorse `componentView_unionFindJoin` over the WHOLE arc list of ANY `WiringDesc` (crossing
included), transporting the same-component boolean view through a `sigma`-relabeling of the endpoint node lists
and matching the loop counts, with forest stability by `isUnionFindForest_stepWiringArcs`.  This is the
SAME-ORDER relabeling leg of the block-swap `componentComm`, the reusable half the adjunction kit never built.
`= true`. -/
def fxBrauer_hasStepWiringArcsComponentView : Bool := true

/-- **Honesty marker — the residual reduction is SHARPENED to the block-swap witness.**
`wiringDescDisjointWindowFresh_of_componentRenameRel` reduces `WiringDescDisjointWindowFresh` through the
engine-agnostic `extractDiagram_of_matchingComponentRenameRel` to constructing a `MatchingComponentRenameRel`
between the two window-disjoint firing orders, so the residual is EXACTLY the block-swap witness
(`sigma = blockRotate`).  `= true`. -/
def fxBrauer_hasWiringDescResidualReduction : Bool := true

/-- **Honesty marker — the block-swap witness's ORDER-SWAP `componentComm` is the standing open leg.**  Its
same-order relabeling half is closed (`stepWiringArcs_componentView`); the cross-order half — that folding
`descA`'s arcs then `descB`'s versus `descB`'s then `descA`'s reaches `sigma`-corresponding union-find PARTITIONS
(join-order independence of the closure, together with `blockRotate`'s `bnodeCorr` and the cyclomatic `loopsEq`)
— is the SAME open witness the adjunction keystone rides (`fxMode_hasMatchingComponentCoreSwapWitness`,
`MatchingGodementComponentCoreSwap`), now confirmed shared with the generic `stepWiring` engine.  NOT discharged.
`= false`. -/
def fxBrauer_hasWiringDescBlockSwapWitness : Bool := false

end FX1Poly.Polygraph
