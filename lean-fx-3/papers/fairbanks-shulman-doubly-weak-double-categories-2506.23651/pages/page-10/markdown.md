10

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

$f, g, h$ could be bracketed as $(fg)h$, $(f1)(gh)$, $((fg)h)(11)$, or infinitely many other ways. By the coherence theorem for bicategories, for any two bracketings of a path of 1-cells there is a canonical rebracketing isomorphism between them built from coherence isomorphism.

**Proposition 2.5.** Given a bicategory $\mathcal{C}$, the following data amount to a represented implicit 2-category:

- The 0-cells and 1-cells are as in $\mathcal{C}$.
- A 2-cell from $s_1, \ldots, s_m$ to $t_1, \ldots, t_n$ is a family consisting of a 2-cell in $\mathcal{B}$ for every possible bracketing of the source and target, such that these 2-cells are related by composing with the appropriate rebracketing coherence isomorphisms (a.k.a. a clique morphism).
- Composition of 2-cells (including identities) is induced by composition of 2-cells in $\mathcal{C}$.
- The composition isomorphisms are given by identities.

Proof. The coherence theorem for bicategories guarantees that each 2-cell from a bracketed form of $s_1 \cdots s_m$ to a bracketed form of $t_1 \cdots t_n$ determines, by composing with coherence isomorphisms, a unique corresponding 2-cell for every rebracketing of the source and target. Thus composition is well-defined, since rebracketing then composing 2-cells is the same as composing then rebracketing as appropriate. The axioms follow from coherence and the bicategory axioms. □

We call this the “underlying implicit 2-category” of a bicategory. Similarly, using coherence for pseudofunctors, we have:

**Proposition 2.6.** A pseudofunctor between bicategories $\mathcal{F}: \mathcal{C} \to \mathcal{D}$ induces a functor (not necessarily preserving chosen composition isomorphisms) between the underlying implicit 2-categories as follows:

- The maps of 0-cells and 1-cells are as in $\mathcal{F}$.
- The map on 2-cells is by applying $\mathcal{F}$ and composing with pseudofunctor coherence isomorphisms. (2-cells in $\mathcal{C}$ between $\mathcal{C}$-bracketed paths of 1-cells map to 2-cells in $\mathcal{D}$ between $\mathcal{D}$-bracketed paths of corresponding 1-cells.)

Moreover, this defines a functor $\mathbf{W}$-2-Cat $\to$ I-2-Cat. □

Next we see this functor $\mathbf{W}$-2-Cat $\to$ I-2-Cat is fully faithful, and its image consists of the representable implicit 2-categories.

**Proposition 2.7.** Given a represented implicit 2-category $\mathbf{C}$, the following data amount to a bicategory:

- The 0-cells are the 0-cells in $\mathbf{C}$.
- The category $\operatorname{Hom}(A, B)$ is the category of bigons between $A$ and $B$ in $\mathbf{C}$.
- Composition and identity for 1-cells is as in $\mathbf{C}$.
- Horizontal composition of 2-cells is by horizontally composing bigons in $\mathbf{C}$, and converting to a bigon (by vertically composing with composition