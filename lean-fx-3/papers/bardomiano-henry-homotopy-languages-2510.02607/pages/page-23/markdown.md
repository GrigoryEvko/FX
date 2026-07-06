Proof. Defining the validity of formulas as in theorem 2.27 it is immediate to verify all the explicit conditions of the inductive definition given in theorem 2.8 simply because the map $\mathbb{L}_{\lambda}^{\mathcal{C}} \to \mathcal{P}(M)$ is a morphism of $\lambda$-boolean algebras. Hence, it immediately follows by induction on formulas that the two definitions are equivalent. $\square$

Construction 2.29. Let $F : \mathcal{C} \to \mathcal{D}$ be a morphism of clans. And let $\mathbb{L}_{\lambda}^{\mathcal{C}}$ and $\mathbb{L}_{\lambda}^{\mathcal{D}}$ be their respective initial $\lambda$-boolean algebras. From the fact that $\mathbb{L}_{\lambda}^{\mathcal{C}}$ is initial, there is a morphism of $\lambda$-boolean algebras

$$\alpha^F : \mathbb{L}_{\lambda}^{\mathcal{C}} \to F^* \left( \mathbb{L}_{\lambda}^{\mathcal{D}} \right).$$

For any $\Gamma \in \mathcal{C}$ and any formula $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{C}}(\Gamma)$ we denote $F(\Phi) := \alpha_{\Gamma}^F(\Phi)$ which is a formula in context $F(\Gamma)$ i.e., an element of $\mathbb{L}_{\lambda}^{\mathcal{D}}(F(\Gamma))$. The following is immediate from the definition above:

Proposition 2.30. Let $M : \mathcal{D} \to \mathbf{Set}$ a model of the clan $\mathcal{D}$, $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{C}}(\Gamma)$ a formula in context $\Gamma$ and $x \in M(F(\Gamma))$. Then, $M \vdash \alpha_F(\Phi)(x)$ if and only if $F^*M \vdash \Phi(x)$.

Of course this also applies to models of a generalized $\kappa$-algebraic theory.

Finally, we finish this section by showing the key property of invariance of formulas along anodyne fibrations. An invariance property will be established in the next section assuming we are working with a model category, but this first invariance property is purely algebraic. This is also the key observation in Makkai FOLDS [Mak95] and it is directly inspired from it.

We start with the following observation: let $\mathcal{C}$ be a clan and $f : M \to N$ a morphism of two $\mathcal{C}$-models, then we have an obvious map $f^* : \mathcal{P}(N) \to \mathcal{P}(M)$ which sends a subset $A \subset N(c)$ for $c \in \mathcal{C}$ to

$$f_c^{-1}(A) \subset M(c)$$

this map is easily seen to be a weak morphism of boolean algebras over $\mathcal{C}$. It is compatible with the boolean algebra operations and the ordinary contravariant functoriality, but it does not have to be compatible with the covariant functoriality $\exists_\pi$ along fibrations. However, one has:

Lemma 2.31. Let $\mathcal{C}$ be a clan and let $f : M \to N$ be a morphism between two $\mathcal{C}$-models. Then $f$ is an anodyne fibration if and only if $f^* : \mathcal{P}(N) \to \mathcal{P}(M)$ is a morphism of $\lambda$-boolean algebras.

23