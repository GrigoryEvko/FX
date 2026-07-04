import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowFactorization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # DisjointWindowSwap — the realized adjacent swap at the seed (ARC-2b brick ii-b)

Brick (ii-a) produced the whisker factorization; this brick APPLIES it: two adjacent
boundary-chained seed atoms whose windows are separated by a gap genuinely TRANSPOSE — the pair
is literally an instance of the `SpineAtomSwap` constructor's redex shape, and the swap fires.
The moved atoms are described EXPLICITLY as record updates of the originals:

  * the moved second atom keeps its generator, boundaries, and right context, with its left
    context re-threaded through the first atom's SOURCE 1-cell (the window slides by the
    first generator's arity change);
  * the moved first atom keeps its generator, boundaries, and left context, with its right
    context re-threaded through the second generator's TARGET 1-cell;
  * the inert middle path is returned with its gap-length pin, so the peel's bubbling
    iteration can recompute windows after the move.

The single mismatch between the factorization's shape and the constructor's redex is one
`composePath` association, bridged by `composePath_assoc`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The realized disjoint-window swap.**  Adjacent seed atoms at chained boundaries with the
second window a `windowGap` to the right of the first's produced window transpose by a genuine
`SpineAtomSwap`: the factorization (ii-a) exhibits the constructor's whisker shape (up to one
`composePath_assoc`), and the swap fires with the moved atoms given as record updates — the
second atom's left context re-threads through the first's source 1-cell, the first atom's right
context re-threads through the second's target 1-cell, everything else unchanged.  The inert
path's gap-length pin rides along for the peel's window bookkeeping. -/
theorem adjunctionSpineAtomSwap_of_disjointWindows
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length) :
    ∃ inertPath : ModalityPath adjunctionGraph atomFirst.rightMidMode atomSecond.leftMidMode,
      inertPath.length = windowGap
        ∧ SpineAtomSwap adjunctionModeSignature
            (atomFirst :: atomSecond :: rest)
            ({ atomSecond with
                leftContext :=
                  composePath (composePath atomFirst.leftContext atomFirst.generatorDom)
                    inertPath }
              :: { atomFirst with
                    rightContext :=
                      composePath (composePath inertPath atomSecond.generatorCod)
                        atomSecond.rightContext }
              :: rest) := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    adjunctionSpineAtom_contextsFactor_of_disjointWindows atomFirst atomSecond boundariesChain
      windowGap windowsDisjoint
  refine ⟨inertPath, inertLength, ?_⟩
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorDomB rightContextB]
  exact SpineAtomSwap.swap generatorA generatorB leftContextA inertPath rightContextB rest

/-! ## Honesty marker -/

/-- **Honesty marker — the realized disjoint-window swap is SHIPPED (ARC-2b brick ii-b).**
`adjunctionSpineAtomSwap_of_disjointWindows` fires a genuine `SpineAtomSwap` on any adjacent
boundary-chained seed pair with a right-of window gap, with the moved atoms explicit (record
updates) and the inert gap pin returned for window bookkeeping.  NOT yet shipped: the mirrored
LEFT-of direction (the peel may bubble past atoms on either side), the chain-preservation
helper for threading the swapped pair back into `SpineBoundaryChained`, and the cup/cap peel
itself (iii) — the sole residual of the seed reconstruction.  `= true`. -/
def fxMode_hasRealizedDisjointWindowSwap : Bool := true

end FX1Poly.Polygraph
