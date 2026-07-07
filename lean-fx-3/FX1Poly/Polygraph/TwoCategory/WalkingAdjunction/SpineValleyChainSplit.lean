import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain

/-! # mode-3 keystone — Piece I realization: split a boundary-coherent chain at an arbitrary list-append

The cell descent locates its redex as a SPINE split `capPrefix ++ cupAtom :: capAtom :: suffixRest`
(`readbackSplit_exposesRedex`).  To feed the shipped STRAIGHTEN / COMMUTE cell moves the located pair must be
exhibited in the right-nested `vcomp` readback shape `preReadback ⊟ (cupFrame ⊟ (capFrame ⊟ tailReadback))`.  The
shipped realization (`RealizedSpineChain` + `chainToCell`, a boundary-coherent chain whose readback is exactly the
right-nested reassembly, faithful on spines by `chainToCell_spine`, a homomorphism up to conversion by
`chainToCell_concat`) hands the readback in that shape ONCE the chain is decomposed at the located position.  The
one missing brick — flagged as the sole open realization residual — is that decomposition: splitting a realized
chain at an ARBITRARY list-append of its atom list.  The `ChainSplit`/`spineChainSplit` kit only splits along a
sub-cell's `spineDiff` contribution, not at a bare `xs ++ ys` boundary.

This file ships it:

  * ★ **`RealizedChainSplit`** — the split witness: a middle boundary path, a left chain over `xs`, a right chain
    over `ys`, and — the payoff of the boundary-coherent index over a flat length shadow — the on-the-nose
    reassembly `concatRealizedChain leftChain rightChain = chain`.  The middle boundary path is NAMED by the
    split (the realized chain can be walked to the boundary the flat Nat-length prop cannot address).
  * ★ **`chainAppendSplit`** — the split itself, by structural recursion on `xs`: peel one `cons` of the chain per
    `cons` of `xs`; the totality is free because the realized chain carries the intermediate anchor path in its
    index.  Zero cast: the boundary coherence walks with the recursion.
  * ★ **`chainToCell_splitReadback`** — the readback consequence: `chainToCell chain` is `TwoCellConv` to
    `chainToCell leftChain ⊟ chainToCell rightChain` (the forward homomorphism `chainToCell_concat` applied to the
    reassembly), i.e. the located split is realized as the vertical composite the cell moves consume.

Raw Lean 4 + Init; the split is structural recursion on `xs` (the impossible nil-chain case rejected by
`List.noConfusion` on the atom-list equation, the cons case by `injection`), the readback consequence is the
shipped `chainToCell_concat` transported along `reassembles`.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-- The **split witness** of a boundary-coherent chain at a list-append `xs ++ ys` of its atoms: a middle
boundary path, a left chain realizing `xs`, a right chain realizing `ys`, and the on-the-nose reassembly back to
the original chain.  The middle path is NAMED — the payoff of the realized (path-indexed) chain over the flat
Nat-length prop, which cannot address the split's boundary. -/
structure RealizedChainSplit (signature : ModeSignature) {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (chain : RealizedSpineChain signature sourcePath targetPath)
    (leftAtomList rightAtomList : List (SpineAtom signature sourceMode targetMode)) where
  /-- The boundary 1-cell where the two sub-chains meet. -/
  midPath : ModalityPath signature.graph sourceMode targetMode
  /-- The sub-chain realizing the left atom list. -/
  leftChain : RealizedSpineChain signature sourcePath midPath
  /-- The sub-chain realizing the right atom list. -/
  rightChain : RealizedSpineChain signature midPath targetPath
  /-- The left sub-chain's atoms are exactly `leftAtomList`. -/
  leftAtoms : chainAtoms leftChain = leftAtomList
  /-- The right sub-chain's atoms are exactly `rightAtomList`. -/
  rightAtoms : chainAtoms rightChain = rightAtomList
  /-- Concatenating the two sub-chains recovers the original chain on the nose. -/
  reassembles : concatRealizedChain leftChain rightChain = chain

/-- ★ **Split a boundary-coherent chain at an arbitrary list-append of its atoms.**  Structural recursion on the
left atom list: the empty split puts everything on the right (`nil` on the left), the cons split peels one atom
off the chain to match the atom peeled off the left list.  The realized chain's index carries the intermediate
anchor path, so the middle boundary is always addressable — the totality the flat Nat-length prop cannot give. -/
def chainAppendSplit {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (leftAtomList rightAtomList : List (SpineAtom signature sourceMode targetMode)) →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (chain : RealizedSpineChain signature sourcePath targetPath) →
    chainAtoms chain = leftAtomList ++ rightAtomList →
    RealizedChainSplit signature chain leftAtomList rightAtomList
  | [], _, _, _, chain, atomsEq =>
      ⟨_, RealizedSpineChain.nil _, chain, rfl, atomsEq, rfl⟩
  | _ :: _, _, _, _, RealizedSpineChain.nil _, atomsEq => by
      exact nomatch atomsEq
  | headAtom :: leftTail, rightAtomList, _, _, RealizedSpineChain.cons atom rest, atomsEq => by
      injection atomsEq with headEq tailEq
      subst headEq
      let subSplit := chainAppendSplit leftTail rightAtomList rest tailEq
      exact
        { midPath := subSplit.midPath
          leftChain := RealizedSpineChain.cons atom subSplit.leftChain
          rightChain := subSplit.rightChain
          leftAtoms := congrArg (atom :: ·) subSplit.leftAtoms
          rightAtoms := subSplit.rightAtoms
          reassembles := congrArg (RealizedSpineChain.cons atom) subSplit.reassembles }

/-- ★ **The readback of a split chain is the vertical composite of the sub-chains' readbacks.**  Transport the
forward homomorphism `chainToCell_concat` along the on-the-nose reassembly: the located split's cell is
`TwoCellConv` to `chainToCell leftChain ⊟ chainToCell rightChain`, exactly the shape the STRAIGHTEN / COMMUTE cell
moves consume. -/
theorem chainToCell_splitReadback {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {chain : RealizedSpineChain signature sourcePath targetPath}
    {leftAtomList rightAtomList : List (SpineAtom signature sourceMode targetMode)}
    (split : RealizedChainSplit signature chain leftAtomList rightAtomList) :
    TwoCellConv signature (chainToCell chain)
      (RawTwoCellExpr.vcomp (chainToCell split.leftChain) (chainToCell split.rightChain)) := by
  have homomorphism := chainToCell_concat split.leftChain split.rightChain
  rw [split.reassembles] at homomorphism
  exact homomorphism

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the sole open realization residual (split-a-realized-chain-at-an-arbitrary-append) is
SHIPPED.**  `chainAppendSplit` decomposes any boundary-coherent chain at an arbitrary `xs ++ ys` boundary of its
atom list into a left chain over `xs`, a right chain over `ys`, and the on-the-nose reassembly
(`RealizedChainSplit.reassembles`); `chainToCell_splitReadback` reads that back as the vertical composite
`chainToCell leftChain ⊟ chainToCell rightChain` via the shipped forward homomorphism `chainToCell_concat`.  So
the located spine split `capPrefix ++ cup :: cap :: rest` is realized as the right-nested `vcomp` shape the cell
STRAIGHTEN / COMMUTE moves consume.

  What this marker does NOT close: the cell-to-chain realization itself (`cellChain` +
  `cellChain_readback_convFull`, shipped one layer over in `FreeTwoCell`), the `SaturatedTwoCellConv`-valued mixed
  driver that dispatches and accumulates the moves, nor the reduction to Piece II.  This is the realization
  BRICK; it flips no gate.  `= true`. -/
def fxMode_hasRealizedChainAppendSplit : Bool := true

end FX1Poly.Polygraph
