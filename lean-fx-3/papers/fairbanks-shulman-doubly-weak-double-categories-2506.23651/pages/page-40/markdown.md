40

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

The equivalence of Proposition 7.10 can also be extended to pseudofunctors. For double bicategories, these are the morphisms in Verity's category $\underline{Horiz}_{SH}$, whose definition is obtained by combining [Ver92, Definition 1.4.7, the definition preceding Lemma 1.4.9, and the definition preceding Observation 1.4.10].

**Definition 7.14.** Let $\mathbf{C}$ and $\mathbf{D}$ be double bicategories. A **double pseudofunctor** $\mathbf{C} \rightarrow \mathbf{D}$ consists of:

- Two pseudofunctors from the vertical and horizontal bicategories of $\mathbf{C}$ to those of $\mathbf{D}$, which are the same on objects.
- A function from squares of $\mathbf{C}$ to squares of $\mathbf{D}$ that acts on boundaries as the 1-cell action of the horizontal and vertical pseudofunctors.
- The top, bottom, left, and right actions of bigons on squares are preserved.
- The horizontal and vertical square composition and identities are preserved, modulo the coherence cells for the horizontal and vertical pseudofunctors.

These are the morphisms of a category **DblBicat**.

**Lemma 7.15.** *Any pseudofunctor between doubly weak double categories induces a double pseudofunctor between their underlying double bicategories.*

*Proof.* Just like Proposition 2.8. $\square$

**Lemma 7.16.** *If $G : \mathbf{C} \rightarrow \mathbf{D}$ is a double pseudofunctor between double bicategories, the following defines a pseudofunctor of doubly weak double categories $FG : F\mathbf{C} \rightarrow F\mathbf{D}$, where $F$ is as in Proposition 7.5.*

- *The action on 0-cells and 1-cells is as for $G$.*
- *Given a 2-cell with some boundary, its component with a given bracketing of the boundary is sent to the image of that 2-cell under $G$, acted on all four sides by the coherence isomorphisms for that bracketing induced by the horizontal and vertical pseudofunctor parts of $G$.*

*Proof.* Coherence for pseudofunctors implies that the operation on 2-cells is well-defined, and preserves composition of 2-cells. $\square$

**Proposition 7.17.** *The equivalence of Proposition 7.10 extends to an equivalence between WDblCat and the full subcategory of DblBicat determined by the tidy double bicategories.* $\square$

*Remark 7.18.* If $\mathbf{C}$ and $\mathbf{D}$ are strict double categories regarded as double bicategories, then a double pseudofunctor as in Definition 7.14 specializes to the notion of double pseudofunctor from [Shu11, Definition 6.1].

Finally, we can further clarify the relationship between doubly weak double categories and "untidy" double bicategories as follows.

**Lemma 7.19.** *The algebras of the monad on BiDblGph induced by the forgetful functor WDblCat$_{\text{st}} \rightarrow \text{DblGph}$ are precisely double bicategories.*

*Proof.* First we observe that the free doubly weak double category on a double graph with bigons is such that the 1-cells are bracketed paths, and the 2-cells are grids of squares with sequences of vertical or horizontal bigons placed at the vertical and horizontal edges, matching along 1-cells, with boundaries bracketed arbitrarily.