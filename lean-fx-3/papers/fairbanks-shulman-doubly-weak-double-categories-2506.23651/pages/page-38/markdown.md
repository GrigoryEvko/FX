38

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

*Remark 7.4.* Double bicategories are monadic over double graphs, essentially by construction. But *tidy* double bicategories are not, since the domains of the additional square-to-bigon conversion operations are not objects of **BiDblGph**: there is no double graph with bigons representing, say, a “square whose vertical source and target are identities”.

All of the operations and laws in a (tidy) double bicategory are readily derived from those in a doubly weak double category, and so there is a forgetful functor $U: \mathbf{WDblCat}_{\text{st}} \rightarrow \mathbf{DblBicat}_{\text{st}}$, where $\mathbf{DblBicat}_{\text{st}}$ denotes the category of double bicategories and strict functors, i.e. homomorphisms of the algebraic structure. In the other direction, we have a functor described as follows (similarly to Proposition 2.5), which will turn out to be left adjoint to this forgetful functor.

**Proposition 7.5.** *Given a double bicategory $\mathcal{C}$, the following data amount to a doubly weak double category $F\mathcal{C}$:*

- *The 0-cells and 1-cells (horizontal and vertical) are as in $\mathcal{C}$.*
- *A 2-cell with a given boundary is a family consisting of a choice of square in $\mathcal{C}$ for every possible bracketing of the boundary, such that these squares are related by composing with the appropriate rebracketing coherence isomorphism bigons.*
- *Composition (and identity) for 2-cells is induced by composition of squares in $\mathcal{C}$.*
- *The composition isomorphisms are given by identity squares.*

*Proof.* Due to the compatibilities of the bigon actions, the coherence theorem for bicategories guarantees that each square with bracketed paths along its boundary determines, by composing with coherence isomorphisms, a unique corresponding square for every rebracketing of the boundary. Thus composition of 2-cells is well-defined, since rebracketing then composing squares is the same as composing then rebracketing as appropriate.

Finally, composition of 2-cells is horizontally and vertically associative and unital by the naturality conditions relating associators and unitors with squares. It satisfies interchange laws because the square composition operations do. $\square$

*Remark 7.6.* The only use of bigons in this definition is to rebracket squares. Hence this construction discards the two bicategories of bigons; only when the double bicategory is tidy can these two bicategories be recovered from the bracketed squares and their composition. Surprisingly, however, although it forgets this information it is still left adjoint to the forgetful functor.

**Lemma 7.7.** *Any doubly weak double category $\mathcal{C}$ is isomorphic to $FUC$.*

*Proof.* By composing with chosen isomorphisms, the 2-cells with arbitrary boundary are in composition-respecting correspondence with bracketed squares. $\square$

**Lemma 7.8.** *In any double bicategory $\mathcal{C}$, the canonical map converting horizontal bigons to squares induces a strict functor from the horizontal bicategory of $\mathcal{C}$ to the horizontal bicategory of $F\mathcal{C}$. (Likewise for the vertical bicategory.) Hence in the case of a tidy double bicategory, this is a strict isomorphism of bicategories.*

*Moreover, this assignment preserves the action of bigons on squares.*