endomorphism monad and one can use the universal property of the colimits for maps to endomorphism monads. Alternatively, one can also use the description of colimits given above: given that the associated monad functor sends each theory $T$ to a monad $\mu^T$ such that $T$-models get identified functorially with $\mu^T$-algebras, it is enough to check that the (contravariant) functor sending each pretheory to its category of models send colimits to limits. But this follows immediately from the fact that $\mathcal{C} \mapsto \Pr(\mathcal{C}) \simeq \operatorname{Fun}(\mathcal{C}^{op}, \mathcal{S})$ send colimits to limits. $\square$

To make this useful, one needs to provide a large supply of nervous monads. The next step is 6.4 that essentially claims that all accessible monads are nervous monads.

Following [2], one defines:

**Definition 6.2.** Let $\mathcal{A} \subset \mathcal{E}$ be a full subcategory. Let $M$ be a monad on $\mathcal{E}$. One says that $M$ is a *monad with arities in $\mathcal{A}$* if for each $X \in \mathcal{E}$, the canonical colimit

$$X \simeq \operatorname{Colim}_{a \in \mathcal{A}/X} a$$

is preserved the composite

$$\mathcal{E} \xrightarrow{M} \mathcal{E} \xrightarrow{i} \Pr(\mathcal{A}),$$

where $i$ denotes the (fully faithful) restricted Yoneda embeddings.

As in the 1-categorical case, we will show that all monads with arities in $\mathcal{A}$ are in fact $\mathcal{A}$-nervous. The proof follows essentially the same strategy as in [2]. Note that the converse is not true, it is shown in [4] that the free groupoid monad on the category of graphs is an example of a $\mathcal{A}$-nervous monad which is not a monad with arities in $\mathcal{A}$, for $\mathcal{A}$ the full subcategory of linear graphs.

**Theorem 6.3.** *Suppose that we have a commutative square of $\infty$-categories*

$$\begin{array}{c} U \xrightarrow{\Phi} V \\ R_1 \downarrow \quad \downarrow R_2 \\ A \xrightarrow{\Psi} B \end{array}$$

*where:*

38