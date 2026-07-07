import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChainBridge
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainAnchor

/-! # mode-3 keystone — Piece I COMMUTE producer, brick 1: the transposed `next` via framed chain surgery

`SpineValleyCommuteLift` reduced the oracle's COMMUTE branch to exhibiting `next` — a cell PARALLEL to
`cell` whose spine is `cell`'s with the located cup·cap pair transposed to a slot-preserving cap·cup pair — plus
the flat `SpineAtomSwap`.  This file ships `next`, the boundary-PATH-level chain surgery the prior markers
flagged as the genuine open node, and it is CLEAN: the `FramedSpineChain` carries its inter-atom boundary
coherences in the ATOM-LIST index, so the middle-pair inversion is TOTAL (`tailChain`, no indexed-inductive
inversion), and re-consing the swapped pair needs only three boundary-PATH equalities (`castSource` seams)
supplied by the caller.

  * ★ **`framedChain_consSource`** — a chain over a cons list has its source AT the head atom's frame source
    (`cases` on the chain — the empty case is impossible by the list index, the cons case is `rfl`).  This is
    the source read-off that anchors every cons peel.
  * ★ **`framedChain_pairPathCoherence`** — from a chain over `prefixCells ++ cupAtom :: capAtom :: rest`, the
    located pair's inter-atom boundary path coherence `atomFrameTarget cupAtom = atomFrameSource capAtom`
    (peel the prefix with `tailChain`, then read the source off the tail).  The path-level upgrade of the
    length-only `SpineBoundaryChained` discipline, for free from the chain's own index.
  * ★ **`framedSwapPrefixChain`** — the surgery: given three boundary-PATH coherences relating the moved
    atoms' frames to the original pair's, transpose the located pair inside ANY chain over
    `prefixCells ++ cupAtom :: capAtom :: rest`, producing a chain over `prefixCells ++ capMoved :: cupMoved
    :: rest` at the SAME source/target.  Structural recursion on `prefixCells` (each cons re-anchored by
    `framedChain_consSource`); the base case extracts the rest chain by `tailChain.tailChain` and re-cons the
    moved pair through the three `castSource` seams.  Signature-generic — the coherences are the caller's.
  * ★ **`commuteNextCell` / `commuteNextCell_spine`** — package the transposed `next`: realize `cell` as its
    own chain (`cellChain`), cast the atom index along `sourceSplit`, run `framedSwapPrefixChain`, and read
    back.  `next` is parallel to `cell` by construction, and its spine is `prefixCells ++ capMoved :: cupMoved
    :: rest` by `readback_spine` — exactly the `targetSplit` the COMMUTE builder consumes.

## What this does NOT close (gates stay `false`)

This ships `next` GIVEN the three boundary-path coherences and the located split.  The coherences themselves,
and the flat `SpineAtomSwap`, are the disjoint-window derivation (brick 2) — supplied at the adjunction from
the classifier's `disjointWindows` verdict.  And the whole COMMUTE branch is only ONE half of the oracle
(STRAIGHTEN stays coupled to Piece II), so `CellDescentStepOracle` stays UN-inhabited and the fib-3 gate flags
stay `false`.

Raw Lean 4 + Init; the source read-off is `cases` on the chain, the surgery is structural recursion on the
prefix threading `castSource`, the packaging is `castAtoms` + `readback_spine`.  `propext`/`Quot.sound`/
`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The source read-off of a chain over a cons list -/

/-- ★ **The source of a chain over a cons list is the head atom's frame source.**  The only constructor whose
atom-list index is a cons is `cons`, whose source index is exactly `atomFrameSource headAtom`; the `nil` case is
excluded by the list index.  This is the read-off every cons peel re-anchors through. -/
theorem framedChain_consSource {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    {headAtom : SpineAtom signature overallSource overallTarget}
    {restAtoms : List (SpineAtom signature overallSource overallTarget)}
    (chain : FramedSpineChain signature sourcePath targetPath (headAtom :: restAtoms)) :
    sourcePath = atomFrameSource headAtom := by
  cases chain with
  | cons _ _ => rfl

/-! ## The located pair's inter-atom boundary path coherence -/

/-- ★ **The located pair chains at the boundary path level.**  From a chain over `prefixCells ++ cupAtom ::
capAtom :: rest`, the inter-atom coherence `atomFrameTarget cupAtom = atomFrameSource capAtom` — peel the
prefix by `tailChain`, then read the head off the pair's tail (`framedChain_consSource`).  The path-level
witness the length-only `SpineBoundaryChained` discipline only records as lengths. -/
theorem framedChain_pairPathCoherence {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cupAtom capAtom : SpineAtom signature overallSource overallTarget}
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (prefixCells : List (SpineAtom signature overallSource overallTarget)) →
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    FramedSpineChain signature sourcePath targetPath
        (prefixCells ++ cupAtom :: capAtom :: rest) →
    atomFrameTarget cupAtom = atomFrameSource capAtom
  | [], _, _, chain => framedChain_consSource chain.tailChain
  | _ :: prefixTail, _, _, chain =>
      framedChain_pairPathCoherence rest prefixTail chain.tailChain

/-! ## The framed-chain surgery: transpose the located pair -/

/-- ★ **Transpose the located pair inside a framed chain.**  Given the three boundary-path coherences relating
the moved atoms' frames to the original pair's — `atomFrameSource capMoved = atomFrameSource cupAtom` (the moved
cap re-anchors at the pair's source), `atomFrameSource cupMoved = atomFrameTarget capMoved` (the moved atoms
chain), `atomFrameTarget cupMoved = atomFrameTarget capAtom` (the moved cup lands at the pair's target) — swap
the located pair inside ANY chain over `prefixCells ++ cupAtom :: capAtom :: rest`, producing a chain over
`prefixCells ++ capMoved :: cupMoved :: rest` at the SAME endpoints.  Structural recursion on `prefixCells`:
each cons is peeled by `tailChain`, re-consed, and re-anchored to the ambient source by `framedChain_consSource`;
the base case extracts the rest chain by `tailChain.tailChain` (totally, thanks to the atom-list index) and
re-cons the moved pair through the three `castSource` seams. -/
def framedSwapPrefixChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cupAtom capAtom capMoved cupMoved : SpineAtom signature overallSource overallTarget}
    (coherenceMovedSource : atomFrameSource capMoved = atomFrameSource cupAtom)
    (coherenceMovedMid : atomFrameSource cupMoved = atomFrameTarget capMoved)
    (coherenceMovedTarget : atomFrameTarget cupMoved = atomFrameTarget capAtom)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (prefixCells : List (SpineAtom signature overallSource overallTarget)) →
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    FramedSpineChain signature sourcePath targetPath
        (prefixCells ++ cupAtom :: capAtom :: rest) →
    FramedSpineChain signature sourcePath targetPath
        (prefixCells ++ capMoved :: cupMoved :: rest)
  | [], _, _, chain =>
      FramedSpineChain.castSource
        (coherenceMovedSource.trans (framedChain_consSource chain).symm)
        (FramedSpineChain.cons capMoved
          (FramedSpineChain.castSource coherenceMovedMid
            (FramedSpineChain.cons cupMoved
              (FramedSpineChain.castSource coherenceMovedTarget.symm
                chain.tailChain.tailChain))))
  | prefixHead :: prefixTail, _, _, chain =>
      FramedSpineChain.castSource (framedChain_consSource chain).symm
        (FramedSpineChain.cons prefixHead
          (framedSwapPrefixChain coherenceMovedSource coherenceMovedMid coherenceMovedTarget
            rest prefixTail chain.tailChain))

/-! ## The transposed `next` cell -/

/-- ★ **The transposed `next` cell.**  Realize `cell` as its own boundary-coherent chain (`cellChain`), cast the
atom-list index along the located `sourceSplit`, run `framedSwapPrefixChain` to transpose the pair, and read
back.  `next` is parallel to `cell` by construction (same `sourcePath ⇒ targetPath`). -/
def commuteNextCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom signature overallSource overallTarget))
    {cupAtom capAtom capMoved cupMoved : SpineAtom signature overallSource overallTarget}
    (coherenceMovedSource : atomFrameSource capMoved = atomFrameSource cupAtom)
    (coherenceMovedMid : atomFrameSource cupMoved = atomFrameTarget capMoved)
    (coherenceMovedTarget : atomFrameTarget cupMoved = atomFrameTarget capAtom)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    RawTwoCellExpr signature sourcePath targetPath :=
  (framedSwapPrefixChain coherenceMovedSource coherenceMovedMid coherenceMovedTarget rest prefixCells
    (FramedSpineChain.castAtoms sourceSplit cell.cellChain)).readback

/-- ★ **The transposed `next` has the swapped spine.**  Its readback's spine is the chain's atom-list index
(`readback_spine`), which is `prefixCells ++ capMoved :: cupMoved :: rest` — exactly the `targetSplit` the
COMMUTE builder consumes. -/
theorem commuteNextCell_spine {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom signature overallSource overallTarget))
    {cupAtom capAtom capMoved cupMoved : SpineAtom signature overallSource overallTarget}
    (coherenceMovedSource : atomFrameSource capMoved = atomFrameSource cupAtom)
    (coherenceMovedMid : atomFrameSource cupMoved = atomFrameTarget capMoved)
    (coherenceMovedTarget : atomFrameTarget cupMoved = atomFrameTarget capAtom)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    (commuteNextCell cell prefixCells rest coherenceMovedSource coherenceMovedMid
        coherenceMovedTarget sourceSplit).spine
      = prefixCells ++ capMoved :: cupMoved :: rest :=
  FramedSpineChain.readback_spine _

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the transposed `next` (COMMUTE brick 1) is SHIPPED via framed chain surgery.**
`framedSwapPrefixChain` transposes the located cup·cap pair inside `cell`'s realized chain — the middle-pair
inversion is TOTAL (`tailChain`, the atom-list index dodges indexed-inductive inversion), and re-consing the
moved pair needs only three boundary-PATH `castSource` seams supplied by the caller.  `commuteNextCell` packages
the readback as a cell parallel to `cell`, with spine `prefixCells ++ capMoved :: cupMoved :: rest`
(`commuteNextCell_spine`) — the `(next, targetSplit)` the COMMUTE builder `cellDescentResult_ofCommutePrefixSwap`
consumes.

  What this marker does NOT close: the three boundary-path coherences + the flat `SpineAtomSwap` are the
  disjoint-window derivation (brick 2), instantiated at the adjunction from the classifier's `disjointWindows`
  verdict.  And the STRAIGHTEN half of the oracle stays coupled to Piece II.  So `CellDescentStepOracle` stays
  UN-inhabited; `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.
  `= true`. -/
def fxMode_hasSpineValleyCommuteNext : Bool := true

end FX1Poly.Polygraph
