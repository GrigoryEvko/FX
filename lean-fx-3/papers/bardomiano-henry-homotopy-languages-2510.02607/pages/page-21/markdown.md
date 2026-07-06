Note that by theorem 2.23, if $T$ is a generalized $\kappa$-algebraic theory, with $\mathcal{C}_T$ its $\kappa$-contextual category, then

$$\mathbb{L}_{\lambda}^{\mathcal{C}_T} = \mathbb{L}_{\lambda}^T.$$

This provides a way to define (or at least to characterize) the first-order language of any clan without having to explicitly give a syntactic description of the clan.

Proof. We can either remark that the $\lambda$-boolean algebras over $\mathcal{C}$ are (by their definition) the models of a multi-sorted $\lambda$-algebraic theory (with one sort for each object $c \in \mathcal{C}$) and hence there is an initial object by usual results on algebraic theories. Alternatively, we can use (see section C) that every clan is equivalent to the contextual category of a generalized algebraic theory and use theorem 2.23 to conclude. □

Next, we mention a few more examples:

### Example 2.25.

1. Let **Set** be the category of sets, considered as a clan where every arrow is a fibration. The contravariant power-set functor $\mathcal{P}: \mathbf{Set}^{op} \to \mathbf{Bool}_{\lambda}$ is a $\lambda$-Boolean algebra over **Set**. The Beck-Chevalley condition follows from theorem 2.26 below.
2. Given $F: \mathcal{C} \to \mathcal{D}$ a morphism of clans, if $\mathcal{B}$ is a $\lambda$-boolean algebra over $\mathcal{D}$, then $F^*\mathcal{B}$ defined by $F^*\mathcal{B}(\Gamma) = \mathcal{B}(F(\Gamma))$ is a $\lambda$-boolean algebra over $\mathcal{C}$.
3. Combining the two observations above, given any model $M$ of a clan $\mathcal{C}$, that is, a morphism of clans $M: \mathcal{C} \to \mathbf{Set}$, one has a boolean algebra $\mathcal{P}(M)$ over $\mathcal{C}$ given by pulling back example 1 along the morphism $M: \mathcal{C} \to \mathbf{Set}$. More explicitly:

$$\begin{array}{rcl} \mathcal{P}(M): & \mathcal{C}^{op} & \to \quad \mathbf{Set} \\ & \Gamma & \mapsto \quad \mathcal{P}(M(\Gamma)). \end{array}$$

Lemma 2.26. Given a square of sets,

$$\begin{array}{c} W \xrightarrow{f} X \\ \downarrow g \qquad \qquad \downarrow h \\ Y \xrightarrow{k} Z, \end{array}$$

21