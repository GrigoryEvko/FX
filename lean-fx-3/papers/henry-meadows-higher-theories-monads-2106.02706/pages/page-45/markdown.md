of $\Pr \mathcal{K}$ of representable presheaves (which is essentially $\mathcal{K}$). As the Yoneda embedding of $\mathcal{K}$ into $\Pr \mathcal{K}$ is natural for this left adjoint/covariant functoriality of $\Pr$ (again by section 6 of [12]), this boils down to a natural equivalence (under $\mathcal{C}$) $\mathcal{C}_{\Omega(F)} \simeq \mathcal{K}$ which concludes the proof. $\square$

## 8 $E_1$, $E_2$ and $E_\infty$-algebras

In this section we show that the monads on the $\infty$-category $\mathcal{S}$ of spaces corresponding to the $E_1$, $E_2$ and $E_\infty$-operads can be seen respectively as 'induced' the free monoid monad on Set, the free braided monoid on groupoids and the free symmetric monoid on groupoids. By induced here we mean that when restricted to appropriate category of arities they corresponds to the same theories.

It should be noted that the $E_2$ and $E_\infty$ operads cannot be described by the framework of planar operads that we recalled in Section 3. It needs the more general 'symmetric' operads framework. We will not recall the details of this and we refer directly to [16]. However, to fix notation, we note that, similarly to how a planar operad is encoded by a map $\mathcal{O}^\otimes \to N(\Delta^{op})$, a symmetric operad is encoded by a map $\mathcal{O}^\otimes \to N(\mathrm{Fin}_*)$ of $\infty$-categories, where $\mathrm{Fin}_*$ is the category of finite pointed sets.

We first recall some basic facts about sifted diagrams:

**Definition 8.1.** An $\infty$-category $K$ is said to be *sifted* if the diagonal map $K \to K \times K$ is cofinal.

*Remark 8.2.* Note that the property of being sifted is invariant under equivalence of $\infty$-categories (see [15, Corollary 4.1.1.10]).

**Lemma 8.3.** *Suppose that $K$ is an $\infty$-category that has finite coproducts. Then $K$ is sifted.*

*Proof.* By [16, 4.1.3.1], it suffices to show that for all $a, b \in K$, $K \times_{K \times K} (K \times K)_{(a,b)/} \cong K_{b/} \times_K K_{a/} \cong K_{\{a,b\}/}$ is weakly contractible. But this $\infty$-category is weakly contractible since it has an initial object, the coproduct of $a, b$. $\square$

We say that an $\infty$-operad $\mathcal{O}^\otimes$ is a *non-colored $\infty$-operad* if its underlying $\infty$-category is terminal, i.e. if $\mathcal{O} \cong \Delta^0$ (see [16, Example 2.1.1.6]). When $\mathcal{O}$ is a non-colored $\infty$-operad, we have a forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{B}) \to \mathcal{B}$ for

45