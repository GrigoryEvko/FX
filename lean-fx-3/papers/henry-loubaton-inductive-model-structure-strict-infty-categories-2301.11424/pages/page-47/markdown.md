**4.29 Theorem.** *The full subcategory of fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$ is isomorphic $\infty$-Cat. Moreover, a morphism between fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$ is a weak equivalence (resp. fibration, resp. acyclic fibration) if and only if the underlying morphism in $\infty$-Cat$_{\text{Can}}$ is a weak equivalence (resp. fibration, resp. acyclic fibration).*

*Proof.* The first claim directly follows from Proposition 4.26 and from the fact that any functor between $\infty$-categories preserves coinductively invertible arrows.

For the second claim, suppose we are given a morphism $p: (X, M) \to (Y, N)$ between fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$. If $U(p)$ is a weak equivalence, so is $p$ by Theorem 4.28

Suppose now that $U(p)$ is an acyclic fibration in $\infty$-Cat$_{\text{Can}}$. The morphism $p$ then as the right lifting property against the set $I^\partial$ (defined in Definition 2.32). To demonstrate that $p$ is an acyclic fibration, it remains to show that an arrow is marked in $X$ if and only if its image in $Y$ is. Since $M$ and $N$ correspond respectively to the set of coinductively invertible arrows of $X$ and $Y$, this follows from Lemma 4.9 of [30].

Finally, suppose that $U(p)$ is a fibration in $\infty$-Cat$_{\text{Can}}$. As $(X, M)$ and $(Y, N)$ are, by definition, fibrant in $\infty$-Cat$^{+\infty}_{\text{Coind}}$, we need to show that $p$ is an isofibration. Applying Lemma 4.9 of [30] to $G_n \to \mathbb{D}_{n-1}$, we find that the marked arrows of $\hat{G}_n$ correspond to coinductively invertible arrows of $G_n$. This marked $\infty$-category is, in particular, fibrant in $\infty$-Cat$^{+\infty}_{\text{Coind}}$. Since $\mathbb{D}_{n-1}^b$ is also fibrant, and since $U$ induces an equivalence between the subcategories of fibrant objects, $p$ has the right lifting property against $\mathbb{D}_{n-1}^b \xrightarrow{t_n^+} (\mathbb{D}_{n-1}, \overline{e_n}) \to \hat{G}_n$. Finally, since $(Y, N)$ has by definition the right lifting property against $(\mathbb{D}_{n-1}, \overline{e_n}) \to \hat{G}_n$, $p$ has the right lifting property against $\mathbb{D}_{n-1}^b \xrightarrow{t_n^+} (\mathbb{D}_{n-1}, \overline{e_n})$ and is thus an isofibration. $\square$

Note that if $m < \infty$, then every $m$-marked $\infty$-category which is fibrant for the saturated inductive left semi-model structure is also fibrant for the coinductive left semi-model structure. Hence, when restricting the previous theorem to $m$-marked objects for $m < \infty$, we no longer need to move to the coinductive left semi-model structure and we directly obtain the following:

**4.30 Corollary.** *If $m < \infty$, the full subcategory of fibrant objects of $\infty$-Cat$^{+m}_{\text{Sat-Ind}}$ is isomorphic to the subcategory of $\infty$-Cat composed of $\infty$-categories whose arrows of dimension strictly superior to $m$ are coinductively invertible. Moreover, a morphism between fibrant $m$-marked $\infty$-categories is a weak equivalence (resp. fibration, resp. acyclic fibration) in $\infty$-Cat$^{+m}_{\text{Sat-Ind}}$ if and only if the underlying morphism in $\infty$-Cat is a weak equivalence (resp. fibration, resp. acyclic fibration) in $\infty$-Cat$_{\text{Can}}$.*

### 4.3 The Canonical Model Structure vs the Limit of the $\pi$-Tower

In this section, we will compare the canonical model structure with the limits of the tower of $\pi$ functors as considered in Section 4.1.

Given a strict $\infty$-category $C$, it is possible to define an $(\infty, m)$ localization $\pi_m X$, and this defines an object of the limit of the tower of $\pi$ functors. But this

47