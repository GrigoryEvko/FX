$$\begin{array}{c} \mathcal{D}' \xrightarrow{G} \mathcal{D} \\ \downarrow V^{-1} \quad \downarrow U \\ \mathcal{C}' \xrightarrow{F} \mathcal{C} \end{array}$$

*if $U$ is a monadic right adjoint functor and $V$ is a right adjoint functor then $V$ is monadic.*

*Proof.* We show that if $U$ satisfies the conditions of Lurie's Barr-Beck monadicity theorem (i.e. Theorem 4.7.3.5 of [15]), then so does $V$.

An arrow $f \in \mathcal{D}'$ is invertible if and only if both its image and $\mathcal{C}'$ and $\mathcal{D}$ are invertible. But if its image in $\mathcal{C}'$ is invertible, then its image in $\mathcal{C}$ is as well. Hence, as $U$ is conservative, its image in $\mathcal{D}$ is also invertible. Thus, $V$ is conservative.

Let $X : \Delta \to \mathcal{D}'$ be a $V$-split simplicial diagram. Its image in $\mathcal{D}$ is a $U$-split simplicial diagram, hence it admit a colimit which is preserved by $U$. The colimit of $X$ in $\mathcal{C}'$ is split, and is thus preserved by $F$, since split colimits are preserved by all functors ([15, Lemma 6.1.3.16]). It follows that $X$ has a colimit both in $\mathcal{D}$ and $\mathcal{C}'$ which is preserved by $U$ and $F$. Hence, it has a colimit in $\mathcal{D}'$ which is preserved by both projections by the lemma below. $\square$

**Lemma 3.24.** *Suppose that we have a diagram*

$$\begin{array}{c} N(I)^{\phi} \xrightarrow{\phi} \mathcal{D} \longrightarrow \mathcal{X} \\ \downarrow \quad \downarrow \quad \downarrow \quad g \downarrow \\ \mathcal{Y} \xrightarrow{f} \mathcal{Z} \end{array}$$

*where the square is a homotopy pullback square of $\infty$-categories and $I$ is any category. Suppose that $\phi$ determines a colimit diagram in $\mathcal{X}, \mathcal{Y}, \mathcal{Z}$. Then $\phi$ is a colimit diagram in $\mathcal{D}$.*

*Proof.* Because of the Quillen equivalence between Bergner's model structure on simplicial categories and Joyal's structure, we can replace the above diagram with the nerve of a diagram of (fibrant) simplicial categories. By [15, 4.2.4.1], we thus reduce to the corresponding statement about simplicial categories, where the homotopy pullback is taken with respect to Bergner's

24