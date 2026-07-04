import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FramedSpineChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction

/-! # RealizedChainBridge — the realized chain rides the generic chain machinery

`RealizedChain` shipped the boundary-coherent chain (`RealizedSpineChain`) with its bespoke
total readback (`chainToCell`) and pinned the cell↔chain bridge obstruction: on the BARE
`TwoCellConv` the readback is NOT convertible to a spine-equal cell (the whisker-functoriality
wall, machine-checked there).  The generic machinery has since moved past that wall:
`FramedSpineChain` carries the same coherence data signature-generically, and the trace-monoid
characterization (`twoCellConvFull_iff_spineTraceEquiv`) closes readback conversion at
`TwoCellConvFull` — the congruence WITH whisker functoriality.  This file joins the two:

  * `RealizedSpineChain.toFramedSpineChain` / `FramedSpineChain.toRealizedSpineChain` — the
    two translations, CAST-FREE both ways (`atomFrameSource`/`atomFrameTarget` unfold to
    exactly the framed chain's `composePath` indices);
  * `toFramedSpineChain_readback` / `toRealizedSpineChain_readback` — the two readbacks are
    the SAME function across the translations (plain equality, structural recursion) — the
    bespoke `chainToCell` is hereby superseded by the generic `FramedSpineChain.readback`;
  * `toFramedSpineChain_spine` / `toRealizedSpineChain_atoms` — the atom lists survive the
    round trip;
  * ★ `RealizedSpineChain.chainToCell_convFull_ofSpineEq` — **the cell↔chain bridge, closed
    at `TwoCellConvFull`**: the readback of a realized chain is convertible to EVERY parallel
    cell whose spine is the chain's atom list.  This is the reconstruction seam the
    `nfReconstruct` residual asked for, delivered one level up (`TwoCellConvFull`, where
    whisker functoriality is a congruence rule) — the bare-`TwoCellConv` obstruction pinned in
    `RealizedChain` still stands and is untouched.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The translations (cast-free both ways) -/

/-- Translate a realized chain onto the generic framed chain: the boundary indices agree
definitionally (`atomFrameSource`/`atomFrameTarget` unfold to the framed `composePath`
indices), so the recursion is cast-free and the atom-list index is the chain's own
`chainAtoms`. -/
def RealizedSpineChain.toFramedSpineChain {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (chain : RealizedSpineChain signature sourcePath targetPath) →
    FramedSpineChain signature sourcePath targetPath (chainAtoms chain)
  | _, _, .nil path => FramedSpineChain.nil path
  | _, _, .cons atom rest =>
      FramedSpineChain.cons atom (RealizedSpineChain.toFramedSpineChain rest)

/-- Translate a framed chain back onto the realized chain (forgetting the atom-list index —
the realized chain recomputes it as `chainAtoms`). -/
def FramedSpineChain.toRealizedSpineChain {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {atoms : List (SpineAtom signature sourceMode targetMode)} →
    FramedSpineChain signature sourcePath targetPath atoms →
    RealizedSpineChain signature sourcePath targetPath
  | _, _, _, .nil boundary => RealizedSpineChain.nil boundary
  | _, _, _, .cons atom rest =>
      RealizedSpineChain.cons atom (FramedSpineChain.toRealizedSpineChain rest)

/-! ## The readbacks agree — the bespoke readback is superseded -/

/-- The generic readback of the translated chain IS the bespoke readback — plain equality,
so `chainToCell` is definitionally subsumed by `FramedSpineChain.readback`. -/
theorem RealizedSpineChain.toFramedSpineChain_readback {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (chain : RealizedSpineChain signature sourcePath targetPath) →
    chain.toFramedSpineChain.readback = chainToCell chain
  | _, _, .nil _ => rfl
  | _, _, .cons atom rest =>
      congrArg (fun restCell => RawTwoCellExpr.vcomp (atomFrame atom) restCell)
        (RealizedSpineChain.toFramedSpineChain_readback rest)

/-- The bespoke readback of the reverse translation IS the generic readback. -/
theorem FramedSpineChain.toRealizedSpineChain_readback {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {atoms : List (SpineAtom signature sourceMode targetMode)} →
    (chain : FramedSpineChain signature sourcePath targetPath atoms) →
    chainToCell chain.toRealizedSpineChain = chain.readback
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons atom rest =>
      congrArg (fun restCell => RawTwoCellExpr.vcomp (atomFrame atom) restCell)
        (FramedSpineChain.toRealizedSpineChain_readback rest)

/-! ## The atom lists survive the round trip -/

/-- The translated chain's readback has the realized chain's own atom list as its spine
(the generic `readback_spine` instantiated across the translation). -/
theorem RealizedSpineChain.toFramedSpineChain_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (chain : RealizedSpineChain signature sourcePath targetPath) :
    chain.toFramedSpineChain.readback.spine = chainAtoms chain :=
  chain.toFramedSpineChain.readback_spine

/-- The reverse translation recomputes exactly the framed chain's atom-list index. -/
theorem FramedSpineChain.toRealizedSpineChain_atoms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {atoms : List (SpineAtom signature sourceMode targetMode)} →
    (chain : FramedSpineChain signature sourcePath targetPath atoms) →
    chainAtoms chain.toRealizedSpineChain = atoms
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons atom rest =>
      congrArg (fun restAtoms => atom :: restAtoms)
        (FramedSpineChain.toRealizedSpineChain_atoms rest)

/-! ## ★ The cell↔chain bridge, closed at `TwoCellConvFull` -/

/-- ★ **The cell↔chain bridge**: the realized chain's readback is `TwoCellConvFull`-convertible
to EVERY parallel cell whose spine is the chain's atom list.  Equal spines are trace-equivalent
by reflexivity, and the trace-monoid characterization reconstructs the conversion.  This is the
reconstruction seam `RealizedChain`'s `nfReconstruct` residual asked for — delivered at
`TwoCellConvFull` (whisker functoriality as a congruence); the bare-`TwoCellConv` obstruction
machine-checked there still stands. -/
theorem RealizedSpineChain.chainToCell_convFull_ofSpineEq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (chain : RealizedSpineChain signature sourcePath targetPath)
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (spineMatches : cell.spine = chainAtoms chain) :
    TwoCellConvFull signature (chainToCell chain) cell :=
  RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv (chainToCell chain) cell
    (by rw [chainToCell_spine chain, spineMatches]
        exact SpineTraceEquiv.refl (chainAtoms chain))

end FX1Poly.Polygraph
