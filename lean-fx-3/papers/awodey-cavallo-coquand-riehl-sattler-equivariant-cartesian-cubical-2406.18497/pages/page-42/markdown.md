4.1. **Groupoid-indexed diagram categories.** We collect some statements about diagram categories indexed by a groupoid. In fact, the first few results apply more generally to category-indexed diagrams.

**Lemma 4.1.1.** *In a diagram category $\mathsf{E}^\mathsf{C}$ whose base category $\mathsf{E}$ has pullbacks, consider a cartesian natural transformation $f: Y \rightarrow X$. The family of evaluation functors $c^*: \mathsf{E}^\mathsf{C} \rightarrow \mathsf{E}$ at objects $c: 1 \rightarrow C$ creates pushforward along $f$.*

*Proof.* The slice of $\mathsf{E}^\mathsf{C}$ over $X$ is the lax bilimit of the categories $\mathsf{E}_{/X(c)}$ indexed over $c \in \mathsf{C}$, with functorial action given by pullback, and similarly for $Y$. For each $u: c \rightarrow d$ in $\mathsf{C}$, there are canonical isomorphisms $f_c^* X_u^* \cong Y_u^* f_d^*$ satisfying coherence under pasting. Thus, the pullback functor $f^*: \mathsf{E}_{/X} \rightarrow \mathsf{E}_{/Y}$ is given by functoriality of lax bilimits from pullback along the components of $f$.

Since the naturality square of $f$ at $u$ is a pullback, the mate $(Y_u)_! f_c^* \rightarrow f_d^*(X_u)_!$ is invertible. By adjointness, so is the mate $X_u^*(f_d)_* \rightarrow (f_c)_* Y_u^*$, assuming we have pushforward along the components of $f$. Therefore, the pullback-pushforward adjunctions at each level assemble into an indexed adjunction. By bifunctoriality of lax bilimits, this gives a right adjoint to pullback along $f$. $\square$

**Lemma 4.1.2.** *In category of diagrams $\mathsf{E}^\mathsf{C}$ whose base category $\mathsf{E}$ has binary products, consider a diagram $A$ with invertible functorial actions. The family of evaluation functors $c^*: \mathsf{E}^\mathsf{C} \rightarrow \mathsf{E}$ at objects $c: 1 \rightarrow C$ creates exponential with $A$ and its right adjoint.*

*Proof.* We argue similarly to the previous proof. The product with $A$ is given bifunctorially from product with $A(c)$ at level $c \in \mathsf{C}$ and invertibility of the map $(-) \times A(c) \rightarrow (-) \times A(d)$ for $u: c \rightarrow d$, using that $A_u$ is invertible. Assuming levelwise exponentials, the induced map on right adjoints $(-)^{A(d)} \rightarrow (-)^{A(c)}$ is invertible. Assuming further right adjoints $(-)^{A(c)} \dashv (-)_{A(c)}$ for $c \in \mathsf{C}$, so is the induced map $(-)_{A(c)} \rightarrow (-)_{A(d)}$. Bifunctoriality of lax bilimits gives the desired right adjoints $(-)^A$ and $(-)_A$. $\square$

**Lemma 4.1.3.** *Consider a category $\mathsf{E}$ with pullbacks and a subobject classifier $1 \rightarrow \Omega$, and the constant diagram functor $\Delta: \mathsf{E} \rightarrow \mathsf{E}^\mathsf{C}$. Then $\Delta 1 \rightarrow \Delta \Omega$ classifies monomorphisms that define cartesian natural transformations in $\mathsf{E}^\mathsf{C}$.*

*Proof.* Note that cartesian natural transformations are closed under pullback and that the claimed classifier is one. Given a cartesian natural transformation that is a componentwise monomorphism, its levelwise classifying squares assemble into a (unique) classifying square by pullback pasting and uniqueness of classification. Since $\mathsf{E}$ has pullbacks, monomorphisms in $\mathsf{E}^\mathsf{C}$ are componentwise monomorphisms. $\square$

For a groupoid $\mathsf{G}$, every functor from $\mathsf{G}$ to $\mathsf{E}$ has invertible functorial action and every natural transformation between such functors is cartesian. Therefore:

**Corollary 4.1.4.** *Consider a locally cartesian closed category $\mathsf{E}$. For each groupoid $\mathsf{G}$, the functor category $\mathsf{E}^\mathsf{G}$ is locally cartesian closed. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves pushforward.* $\square$

**Corollary 4.1.5.** *Consider a cartesian closed category $\mathsf{E}$. For each groupoid $\mathsf{G}$, an object $A \in \mathsf{E}^\mathsf{C}$ is tiny if it is componentwise tiny. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves exponentiation with componentwise tiny objects.* $\square$

**Corollary 4.1.6.** *Consider a finitely complete category $\mathsf{E}$ with a subobject classifier. For each groupoid $\mathsf{G}$, the functor category $\mathsf{E}^\mathsf{G}$ has a subobject classifier. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves subobject classifiers.* $\square$

42