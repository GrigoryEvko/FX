*then the power set functor satisfies the Beck-Chevalley condition on this square, i.e., $k^*\exists_h = \exists_g f^*$ as maps $\mathcal{P}(X) \rightarrow \mathcal{P}(Y)$ if and only if the square is a weak pullback square i.e., if and only if the cartesian gap map $W \rightarrow Y \times_Z X$ is surjective.*

*Proof.* Given a subset $P \subset X$ one has:

$$k^*h!P = \{y \in Y | k(y) = h(p) \text{ for some } p \in P\},$$

$$g!f^*P = \{g(w) | f(w) \in P\}.$$

Surjectivity of the map $W \rightarrow Y \times_Z X$ gives a canonical way to make any element of $k^*h!P$ into an element of $g!f^*P$, and conversely, applying the equality to $P = \{p\}$ produces the surjectivity of $W \rightarrow Y \times_Z X$. $\square$

In this new setting with just a clan $\mathcal{C}$, one can still define the set of formulas $\mathbb{L}_\lambda^\mathcal{C}$ as the initial $\lambda$-boolean algebra over $\mathcal{C}$. We now explain what it means for formulas defined in this way to be “true” or “false” given a model and an interpretation of its variables in the model.

**Construction 2.27.** Given a clan $\mathcal{C}$ and a model of $M : \mathcal{C} \rightarrow \mathbf{Set}$ we have, as explained in theorem 2.25, a $\lambda$-boolean algebra over $\mathcal{C}$ defined by $c \mapsto \mathcal{P}(M(c))$. By initiality of the $\lambda$-boolean algebra $\mathbb{L}_\lambda^\mathcal{C}$, there exists a unique morphism of $\lambda$-boolean algebras over $\mathcal{C}$:

$$|-|_M : \mathbb{L}_\lambda^\mathcal{C} \rightarrow \mathcal{P}(M).$$

This morphism associates each formula $\phi$ in context $\Gamma$ to a subset $|\phi|_M \subseteq M(\Gamma)$. An element $x \in M(\Gamma)$ is said to *satisfy* $\phi$ if $x \in |\phi|_M$. With some abuse of notation, we say that “$\phi(x)$ is true” in this case. We also write

$$M \vdash \phi(x)$$

when we want to insist on which model we are talking about. When $\Gamma$ is the terminal object of $\mathcal{C}$ *i.e.,* $\phi$ is a closed formula, then $M(\Gamma) = \{*\}$. Therefore, $\mathcal{P}(M(\Gamma)) = \{\bot, \top\}$ so that $|\phi|_M$ is simply a proposition. One then says that $M$ satisfies $\phi$, and we write $M \vdash \phi$.

**Lemma 2.28.** *When $\mathcal{C} = \mathcal{C}_T$ is the $\kappa$-contextual category of a $\kappa$-generalized algebraic theory, then through the identification $\mathbb{L}_\lambda^T = \mathbb{L}_\lambda^\mathcal{C}$, the two definitions of validity of a formula on elements of a model given by theorem 2.8 and theorem 2.27 are equivalent.*

22