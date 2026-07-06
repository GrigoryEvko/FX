codiagonals of $k_n$. Remark now that, as $\vec{G}_n \coprod_{(G_n, \vec{\mathbb{S}})} \vec{G}_n = \vec{G}_n$, all the iterated homotopy codiagonals are identities. To conclude, it is enough to show that $X$ has the left lifting property against morphisms $k_n$ for $n > 0$, which is obvious by assumption and by the Proposition 4.22. $\square$

**4.27 Lemma.** *Let $X$ be an $\infty$-category, and let $M$ be the set of coinductive invertible arrows. The canonical morphism $X^\flat \rightarrow (X, M)$ is an anodyne cofibration of the coinductive left semi-model structure.*

*Proof.* We denote by $(X, M')$ the marked $\infty$-category obtained as the pushout of the following span:

$$\coprod_{\operatorname{Hom}(G_n, X)} \vec{G}_n \xleftarrow{\coprod_{P_n}} \coprod_{\operatorname{Hom}(G_n, X)} G_n^\flat \longrightarrow X^\flat$$

By stability by coproducts and pushouts, the canonical morphism $X^\flat \rightarrow (X, M')$ is an anodyne cofibration of the coinductive left semi-model structure.

Moreover, Lemma 4.9 of [30] applied to the acyclic fibration $G_n \rightarrow \mathbb{D}_{n-1}$ implies that any arrow of $G_n$ of dimension higher or equal to $n$ is coinductively invertible. In particular, every marked arrow of $\vec{G}_n$ is coinductively invertible. We then have $M' \subset M$, and 4.22 implies that $M \subset M'$. Furthermore, Proposition 4.26 implies that $(X, M)$ is a fibrant object of the coinductive left semi-model structure. $\square$

**4.28 Theorem.** *The adjunction*

$$(-)^\flat : \infty\text{-}\mathbf{Cat} \xrightarrow{\quad} \infty\text{-}\mathbf{Cat}^{+\infty} : U$$

*induces a Quillen equivalence between $\infty\text{-}\mathbf{Cat}_{Can}$ and $\infty\text{-}\mathbf{Cat}_{Coind}^{+\infty}$.*

*Proof.* We first show that this adjunction is a Quillen adjunction.

Remark that the left adjoint obviously preserves generating cofibrations. Furthermore, for any integer $n$, the morphism

$$\mathbb{D}_n^\flat \xrightarrow{i_n^-} \mathbb{D}_{n+1}^\flat \xrightarrow{k_{n+1}} G_{n+1}^\flat$$

admits a retract given by the weak equivalence $G_{n+1}^\flat \rightarrow \mathbb{D}_n^\flat$, and so it is a acyclic cofibration of $\infty\text{-}\mathbf{Cat}_{Can}^{+m}$. The left adjoint then preserves cofibration and acyclic cofibration, which implies that the adjunction is a Quillen adjunction.

We now show that this adjunction is a Quillen equivalence. Let $X$ be a cofibrant $\infty$-category and let $M$ be the set of coinductive invertible arrows of $X$. The lemma Proposition 4.26 and Lemma 4.27 imply that $(X, M)$ is the fibrant replacement of $X^\flat$. The derived unit then corresponds to the isomorphism $U(X^\flat)_{fib} \cong U(X, M) \cong X$.

Remark now that the right adjoint preserves colimits and cofibrations. It is then sufficient to compute the derived counit on cofibrant and fibrant objects of $\infty\text{-}\mathbf{Cat}_{Coind}^{+\infty}$. Given such an object $(X, M)$, we then have $((U(X, M))_{cof})^\flat \cong X^\flat$. As Proposition 4.26 states that $M$ is the set of coinductive invertible arrows of $X$, Lemma 4.27 implies that the derived counit $X^\flat \rightarrow (X, M)$ is a weak equivalence. $\square$

46