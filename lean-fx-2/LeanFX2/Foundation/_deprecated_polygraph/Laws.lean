import LeanFX2.Foundation._deprecated_polygraph.VerticalComp
import LeanFX2.Foundation._deprecated_polygraph.HorizontalComp

/-! # Strict ω-category laws on `VerticalChain` and `HorizontalChain`.

Per Burroni 1993 §1.1 / §2 and extended-roadmap §2 Definition 2.1, the
free strict ω-category over a polygraph is the quotient of formal
compositions by:

* **Associativity**: `α ∗ (β ∗ γ) = (α ∗ β) ∗ γ`
* **Unit laws**: `id ∗ α = α = α ∗ id`
* **Interchange**: `(α ∗ β) · (γ ∗ δ) = (α · γ) ∗ (β · δ)`
  where `∗` is vertical and `·` is horizontal.

K11.6 ships associativity for both vertical and horizontal chains.
The unit laws were shipped alongside the chain definitions:

* Vertical: `VerticalChain.append_identity_left` / `_identity_right`
  (in `VerticalComp.lean`).
* Horizontal: `HorizontalChain.append_identity_left` / `_identity_right`
  (in `HorizontalComp.lean`).

## Interchange (Eckmann-Hilton) deferral

The interchange law relates vertical composition of `(n+2)`-cells
along `(n+1)`-boundary with horizontal composition of `(n+2)`-cells
along `n`-boundary.  The horizontal chain shipped at K11.5 composes
dim-1 arrows along dim-0 boundary only; horizontal composition of
2-cells (whiskering of 2-cells) requires a separate inductive chain
indexed by 1-cell source/target, deferred to K11.6b.

For the dim-1 / dim-2 specialization that DOES live in scope: in a
1-category (no 2-cells), vertical composition is trivial (every
identity 2-cell composes with itself), so interchange degenerates to
horizontal associativity, which IS shipped here.  Interchange in its
non-degenerate form arrives with K11.6b's higher-dim horizontal
composition. -/

namespace LeanFX2.Foundation._deprecated_polygraph

namespace VerticalChain

/-- Associativity of vertical (sequential) composition.  Sequencing
three chains is independent of how they're parenthesized. -/
theorem append_assoc {dim sv tv : Nat}
    {startCell midOneCell midTwoCell endCell : PolyCell (dim + 1) sv tv}
    (firstChain : VerticalChain startCell midOneCell)
    (secondChain : VerticalChain midOneCell midTwoCell)
    (thirdChainArg : VerticalChain midTwoCell endCell) :
    append (append firstChain secondChain) thirdChainArg =
    append firstChain (append secondChain thirdChainArg) := by
  induction firstChain with
  | identity _ => rfl
  | cons stepWitness sourceMatches targetMatches restChain ih =>
    rw [append_cons_unfold, append_cons_unfold,
        append_cons_unfold, ih]

end VerticalChain

namespace HorizontalChain

/-- Associativity of horizontal (whiskering) composition.  Sequencing
three arrow-chains is independent of how they're parenthesized. -/
theorem append_assoc {sourceVtx midOneVtx midTwoVtx targetVtx : Nat}
    (firstChain : HorizontalChain sourceVtx midOneVtx)
    (secondChain : HorizontalChain midOneVtx midTwoVtx)
    (thirdChainArg : HorizontalChain midTwoVtx targetVtx) :
    append (append firstChain secondChain) thirdChainArg =
    append firstChain (append secondChain thirdChainArg) := by
  induction firstChain with
  | identity _ => rfl
  | cons stepArrow restChain ih =>
    rw [append_cons_unfold, append_cons_unfold,
        append_cons_unfold, ih]

end HorizontalChain

end LeanFX2.Foundation._deprecated_polygraph
