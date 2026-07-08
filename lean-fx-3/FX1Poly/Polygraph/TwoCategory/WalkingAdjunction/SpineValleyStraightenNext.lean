import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteNext

/-! # mode-3 keystone — Piece I STRAIGHTEN producer (iii-a): the DELETED `next` via framed chain surgery

`SpineValleyCommuteNext` shipped the COMMUTE `next` — the transposed cell via `framedSwapPrefixChain` (re-cons the
two moved atoms through three `castSource` seams).  This file ships the STRAIGHTEN analogue, and it is STRICTLY
SIMPLER: deleting a matched cup·cap pair splices the chain via ONE seam — the shipped `cupCapDeletionReconnects`
endpoint identification `atomFrameSource cupAtom = atomFrameTarget capAtom` — instead of re-consing two atoms.

  * ★ **`framedDeletePrefixChain`** — the surgery: given the reconnection `atomFrameSource cupAtom =
    atomFrameTarget capAtom`, delete the located pair inside ANY chain over `prefixCells ++ cupAtom :: capAtom ::
    rest`, producing a chain over `prefixCells ++ rest` at the SAME source/target.  Structural recursion on
    `prefixCells` (each cons re-anchored by `framedChain_consSource`); the base case drops the pair by
    `tailChain.tailChain` and welds the rest chain onto the prefix boundary through the single reconnection
    `castSource` seam.
  * ★ **`straightenNextCell` / `straightenNextCell_spine`** — package the deleted `next`: realize `cell` as its own
    chain (`cellChain`), cast the atom index along `sourceSplit`, run `framedDeletePrefixChain`, and read back.
    `next` is parallel to `cell` by construction, and its spine is `prefixCells ++ rest` by `readback_spine` —
    exactly the `targetSplit` the STRAIGHTEN builder `cellDescentResult_ofStraightenStep` consumes.

## What this does NOT close (gates stay `false`)

This ships `next` (the deleted chain readback) GIVEN the reconnection.  The reconnection is the shipped
`cupCapDeletionReconnects` (from the boundary coherence of a matching cup·cap pair).  What is NOT here: the
`stepConv : SaturatedTwoCellConv cell next` (the readback realization — deletion is NOT trace-preserving, so it
needs the concrete `atomFrame cup ⊟ atomFrame cap ≈ id` collapse fed through the readback chain), and the
assembly + swap.  So `CellStraightenStepInput` stays open; `convOfMapEq` and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; the surgery is structural recursion on the prefix threading `castSource`, the packaging is
`castAtoms` + `readback_spine`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The framed-chain surgery: delete the located pair -/

/-- ★ **Delete the located pair inside a framed chain.**  Given the reconnection `atomFrameSource cupAtom =
atomFrameTarget capAtom` (the shipped `cupCapDeletionReconnects` endpoint identification for a matching cup·cap
pair), drop the located pair inside ANY chain over `prefixCells ++ cupAtom :: capAtom :: rest`, producing a chain
over `prefixCells ++ rest` at the SAME endpoints.  Structural recursion on `prefixCells`: each cons is peeled by
`tailChain`, re-consed, and re-anchored to the ambient source by `framedChain_consSource`; the base case extracts
the rest chain by `tailChain.tailChain` (totally, thanks to the atom-list index) and welds it onto the prefix
boundary through the single reconnection `castSource` seam. -/
def framedDeletePrefixChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cupAtom capAtom : SpineAtom signature overallSource overallTarget}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (prefixCells : List (SpineAtom signature overallSource overallTarget)) →
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    FramedSpineChain signature sourcePath targetPath
        (prefixCells ++ cupAtom :: capAtom :: rest) →
    FramedSpineChain signature sourcePath targetPath (prefixCells ++ rest)
  | [], _, _, chain =>
      FramedSpineChain.castSource
        (((framedChain_consSource chain).trans reconnect).symm)
        chain.tailChain.tailChain
  | prefixHead :: prefixTail, _, _, chain =>
      FramedSpineChain.castSource (framedChain_consSource chain).symm
        (FramedSpineChain.cons prefixHead
          (framedDeletePrefixChain reconnect rest prefixTail chain.tailChain))

/-! ## The deleted `next` cell -/

/-- ★ **The deleted `next` cell.**  Realize `cell` as its own boundary-coherent chain (`cellChain`), cast the
atom-list index along the located `sourceSplit`, run `framedDeletePrefixChain` to drop the pair, and read back.
`next` is parallel to `cell` by construction (same `sourcePath ⇒ targetPath`). -/
def straightenNextCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom signature overallSource overallTarget))
    {cupAtom capAtom : SpineAtom signature overallSource overallTarget}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    RawTwoCellExpr signature sourcePath targetPath :=
  (framedDeletePrefixChain reconnect rest prefixCells
    (FramedSpineChain.castAtoms sourceSplit cell.cellChain)).readback

/-- ★ **The deleted `next` has the spliced spine.**  Its readback's spine is the chain's atom-list index
(`readback_spine`), which is `prefixCells ++ rest` — exactly the `targetSplit` the STRAIGHTEN builder consumes. -/
theorem straightenNextCell_spine {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom signature overallSource overallTarget))
    {cupAtom capAtom : SpineAtom signature overallSource overallTarget}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    (straightenNextCell cell prefixCells rest reconnect sourceSplit).spine
      = prefixCells ++ rest :=
  FramedSpineChain.readback_spine _

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the deleted `next` (STRAIGHTEN producer iii-a) is SHIPPED via framed chain surgery.**
`framedDeletePrefixChain` deletes the located cup·cap pair inside `cell`'s realized chain — the middle-pair drop is
TOTAL (`tailChain.tailChain`, the atom-list index dodges indexed-inductive inversion), and the splice needs only
the single reconnection `castSource` seam supplied by `cupCapDeletionReconnects` (strictly simpler than the COMMUTE
swap's three seams).  `straightenNextCell` packages the readback as a cell parallel to `cell`, with spine
`prefixCells ++ rest` (`straightenNextCell_spine`) — the `(next, targetSplit)` the STRAIGHTEN builder
`cellDescentResult_ofStraightenStep` consumes.

  What this marker does NOT close: the `stepConv : SaturatedTwoCellConv cell next` (the readback realization —
  deletion is NOT trace-preserving, so it needs the concrete `atomFrame cup ⊟ atomFrame cap ≈ id` collapse fed
  through the readback chain), and the assembly + swap.  So `CellStraightenStepInput` stays open;
  `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenNext : Bool := true

end FX1Poly.Polygraph
