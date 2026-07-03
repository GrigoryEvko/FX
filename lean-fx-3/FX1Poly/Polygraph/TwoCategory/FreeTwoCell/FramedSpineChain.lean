import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # FramedSpineChain — the boundary-coherent spine chain + TOTAL readback (FREE-1)

The general (signature-GENERIC) word problem for the FREE 2-category splits into the shipped
soundness (`TwoCellConv.spineTraceEquiv`) and two open obligations; the reconstruction one is
blocked, per `SpineReadback`'s analysis, on a genuine totality obstruction: a bare atom LIST
carries no inter-atom boundary coherence, so no total boundary-indexed readback function on
lists can exist (the empty list forces a reflexive boundary, an atom head forces a rigid one).

This file ships the fix named there — "a coherence-refined chain datatype carrying the
inter-atom boundary equalities":

* `FramedSpineChain signature sourcePath targetPath atoms` — indexed by the source/target
  1-cells AND the atom list; `cons` anchors the chain's source at the head atom's frame source
  and requires the rest to start at its frame target, so every inter-atom boundary equality is
  DEFINITIONAL in the indices — no stored casts, no `dite` coherence chain;
* `FramedSpineChain.readback` — the TOTAL readback: `nil` reads back as the identity 2-cell
  (its indices are reflexive by construction), `cons` as the whiskered generator vertically
  composed with the rest — a right-associated chain at exactly the indexed boundary;
* ★ `FramedSpineChain.readback_spine` — the readback's spine IS the indexed atom list: the
  left whisker context re-enters definitionally (left identity is definitional), the right one
  via `composePath_identityPath_right` + structure eta;
* `append` / `singleton` — chain concatenation (indices concatenate definitionally) and the
  one-atom chain, the assembly pieces the reconstruction induction consumes.

Consumed by FREE-2/3/4 (chain existence for normal forms, the Godement step lifted onto
chains, the generic trace reconstruction) — and through them by BOTH word-problem legs: the
free case directly, the saturated case via triangle-normal forms. -/

namespace FX1Poly.Polygraph

/-! ## The chain datatype -/

/-- The **boundary-coherent spine chain**: a certificate that an atom list composes as a
vertical chain from `sourcePath` to `targetPath`.  `cons` pins the chain's source at the head
atom's frame source (`leftContext ∘ generatorDom ∘ rightContext`) and requires the rest to
start at its frame target — the inter-atom boundary equalities live in the INDICES, so they
are definitional and the readback below is total. -/
inductive FramedSpineChain (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    ModalityPath signature.graph overallSource overallTarget →
    ModalityPath signature.graph overallSource overallTarget →
    List (SpineAtom signature overallSource overallTarget) → Type where
  /-- The empty chain sits at a single (reflexive) boundary. -/
  | nil (boundary : ModalityPath signature.graph overallSource overallTarget) :
      FramedSpineChain signature boundary boundary []
  /-- One atom, then a chain from its frame target onward. -/
  | cons (atom : SpineAtom signature overallSource overallTarget)
      {chainTarget : ModalityPath signature.graph overallSource overallTarget}
      {restAtoms : List (SpineAtom signature overallSource overallTarget)}
      (rest : FramedSpineChain signature
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
        chainTarget restAtoms) :
      FramedSpineChain signature
        (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
        chainTarget (atom :: restAtoms)

/-! ## The total readback -/

/-- ★ **The TOTAL readback past the `spine` quotient** — on chains, where the documented
list-level totality obstruction disappears: the empty chain reads back as the identity 2-cell
at its (reflexive-by-construction) boundary, a `cons` as the whiskered generator vertically
composed with the rest's readback.  The result lands at exactly the indexed boundary — no
casts, no coherence side conditions. -/
def FramedSpineChain.readback {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    {atoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature sourcePath targetPath atoms →
    RawTwoCellExpr signature sourcePath targetPath
  | _, _, _, .nil boundary => RawTwoCellExpr.id boundary
  | _, _, _, .cons atom rest =>
      RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft atom.leftContext
          (RawTwoCellExpr.whiskerRight atom.rightContext
            (RawTwoCellExpr.gen atom.generator)))
        rest.readback

/-! ## The readback hits the indexed spine -/

/-- Rebuilding an atom with its right context composed with the identity path yields the atom
itself — the single propositional seam of the readback's spine computation (the left seam is
definitional). -/
private theorem spineAtomOfRightIdentity {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget) :
    (⟨atom.leftMidMode, atom.rightMidMode, atom.leftContext, atom.generatorDom,
      atom.generatorCod, atom.generator,
      composePath atom.rightContext (identityPath overallTarget)⟩
      : SpineAtom signature overallSource overallTarget) = atom := by
  rw [composePath_identityPath_right atom.rightContext]

/-- ★ **The readback's spine is the indexed atom list.**  Per `cons`, the readback's spine
computes to the rebuilt head atom (left context re-entering definitionally, right context up
to the identity law) consed on the rest's spine — so the total readback is a genuine section
of the `spine` quotient on chained lists. -/
theorem FramedSpineChain.readback_spine {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    {atoms : List (SpineAtom signature overallSource overallTarget)} →
    (chain : FramedSpineChain signature sourcePath targetPath atoms) →
    chain.readback.spine = atoms
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons atom rest => by
      show (⟨atom.leftMidMode, atom.rightMidMode, atom.leftContext, atom.generatorDom,
            atom.generatorCod, atom.generator,
            composePath atom.rightContext (identityPath _)⟩
          : SpineAtom signature _ _) :: rest.readback.spine
        = atom :: _
      rw [spineAtomOfRightIdentity atom, FramedSpineChain.readback_spine rest]

/-! ## Assembly pieces -/

/-- Chain concatenation — the indices concatenate definitionally. -/
def FramedSpineChain.append {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath middlePath targetPath :
      ModalityPath signature.graph overallSource overallTarget} →
    {firstAtoms secondAtoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature sourcePath middlePath firstAtoms →
    FramedSpineChain signature middlePath targetPath secondAtoms →
    FramedSpineChain signature sourcePath targetPath (firstAtoms ++ secondAtoms)
  | _, _, _, _, _, .nil _, second => second
  | _, _, _, _, _, .cons atom rest, second =>
      FramedSpineChain.cons atom (rest.append second)

/-- The one-atom chain at the atom's own frame boundary. -/
def FramedSpineChain.singleton {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget) :
    FramedSpineChain signature
      (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
      (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
      [atom] :=
  FramedSpineChain.cons atom
    (FramedSpineChain.nil
      (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)))

/-! ## Honesty marker -/

/-- **Honesty marker — the boundary-coherent chain + TOTAL readback are SHIPPED (FREE-1).**
The datatype named by `SpineReadback`'s obstruction analysis exists, signature-generic: chains
carry the inter-atom boundary equalities in their indices, the readback is total and lands at
the indexed boundary, and its spine is the indexed atom list (`readback_spine`), with `append`
/ `singleton` assembly.  NOT yet shipped: chain EXISTENCE for a cell's own spine + readback
Conv (FREE-2), the Godement step lifted onto chains (FREE-3), and the generic trace
reconstruction they assemble into (FREE-4) — after which `fxMode_hasSpineTraceReconstruction`
flips.  `= true`. -/
def fxMode_hasFramedSpineChain : Bool := true

end FX1Poly.Polygraph
