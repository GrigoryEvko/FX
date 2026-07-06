and $M$ is $\mathcal{A}$-nervous if and only if this square is a pullback. We conclude by applying Theorem 6.3 to it. Both vertical functors are monadic right adjoint functors (for the right one, it was observed in the proof of Proposition 5.2). The functor $\mathcal{E} \rightarrow \Pr(\mathcal{A})$ is the restricted Yoneda embeddings and is fully faithful because $\mathcal{A}$ is dense in $\mathcal{E}$. On the left hand side the left adjoint is the free algebra functor, and the right hand side it is the left Kan extension of the canonical functor $\mathcal{A} \rightarrow \mathrm{Th}_{\mathcal{A}}(M)$. The natural transformation “$L_2\Psi \rightarrow \Phi L_1$” in the notation of Theorem 6.3 corresponds exactly to the map

$$\mathrm{Colim}_{\mathcal{A}/X} M(a) \rightarrow M(X)$$

where the colimit is taken in $\Pr(\mathrm{Th}_{\mathcal{A}}(M))$. This map is an equivalence if and only if its image in $\Pr(\mathcal{A})$ is an equivalence and this corresponds exactly to the definition of a monad with arities in $\mathcal{A}$. $\square$

**Definition 6.5.** Let $\lambda$ be a regular cardinal. We say that a monad on a $\lambda$-accessible $\infty$-category $C$ is $\lambda$-accessible if its underlying functor is $\lambda$-accessible in the sense of [15, 5.4.2.5]. That is, if it preserves $\lambda$-directed colimits.

**Lemma 6.6.** *Let $T$ be a monad on an $\infty$-category $\mathcal{C}$ whose underlying functor commutes to colimits of $I$-shaped diagrams. Let $(C_i)_{i \in I}$ be an $I$-shaped diagram in $\mathcal{C}^T$, then:*

- *A cocone for $C_i$ in $\mathcal{C}^T$ is a colimit cocone if and only if its image under the forgetful functor is a colimit cocone in $\mathcal{C}$.*
- *If the image under the forgetful functor of $(C_i)$ admits a colimit in $\mathcal{C}$, then the colimit diagram can be lifted into a colimit diagram in $\mathcal{C}^T$.*

*Proof.* Let $\mathrm{End}_I(\mathcal{C}) \subset \mathrm{End}(\mathcal{C})$ be the full subcategory of endofunctors preserving $I$-shaped colimits. As $\mathrm{End}_I(\mathcal{C})$ is stable under composition it is a monoidal subcategory of $\mathrm{End}(\mathcal{C})$ in the sense of section 2.2.1 of [16], and hence it is itself a monoidal $\infty$-category. A monad preserving $I$-shaped colimits can be seen as a monoid object for this subcategory. As $\mathcal{C}$ is also tensored over $\mathrm{End}_I(\mathcal{C})$, applying [16, Corollary 4.2.3.5] to $\mathcal{C} = \mathrm{End}_I(\mathcal{C})$ immediately gives the result claimed. $\square$

40