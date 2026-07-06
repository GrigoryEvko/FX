**2.33 Remark.** It immediately follows from the small object argument that every morphism can be factored into a cofibration followed by an acyclic fibration, and that all cofibrations are retracts of transfinite compositions of pushouts of morphisms in $I$.

**2.34 Proposition.** A morphism $(K, M) \rightarrow (L, N)$ is a cofibration in $\infty$-$\mathbf{Cat}^{+m}$ if and only if the induced functor $K \rightarrow L$ is a cofibration in the canonical model structure $\infty$-$\mathbf{Cat}_{Can}$ recalled in Theorem 4.23.

In particular, the cofibrant objects of $\infty$-$\mathbf{Cat}^{+m}$ are exactly the $m$-marked $\infty$-categories whose underlying $\infty$-category is free on a polygraph, with any possible marking on them.

*Proof.* As recalled in Theorem 4.23, the set of generating cofibrations of the canonical model structure is given by $\{i_n: \partial\mathbb{D}_n \rightarrow \mathbb{D}_n \mid n \geq 0\}$. Note that the trivial marking functor $(-)^b: \infty$-$\mathbf{Cat} \rightarrow \infty$-$\mathbf{Cat}^{+m}$ and the forgetful functor $U: \infty$-$\mathbf{Cat}^{+m} \rightarrow \infty$-$\mathbf{Cat}$ preserve colimits. We can directly deduce that both of these functors preserve cofibrations.

In particular, a cofibration $(K, M) \rightarrow (L, N)$ induces a cofibration $K \rightarrow L$ in $\infty$-$\mathbf{Cat}_{Can}$.

Conversely, suppose we are given a morphism $(K, M) \rightarrow (L, N)$ such that the induced morphism $K \rightarrow L$ is a cofibration in $\infty$-$\mathbf{Cat}_{Can}$. We have a canonical square:

$$\begin{array}{ccc} K^b & \longrightarrow & (K, M) \\ \downarrow & & \downarrow \\ L^b & \longrightarrow & (L, N) \end{array}$$

where the left-hand vertical morphism is a cofibration. The canonical morphism $L^b \coprod_{K^b} (K, M) \rightarrow (L, N)$ is the identity on the underlying category and is thus an iterated pushout of morphisms in $I^{+m}$. In particular, it is a cofibration, and by stability under pushouts and compositions, so is $(K, M) \rightarrow (L, N)$.

Finally, the last claim follows from [35, Theorem 7.4], which asserts that cofibrant objects of $\infty$-$\mathbf{Cat}_{Can}$ correspond to $\infty$-categories that are free on a polygraph. $\square$

**2.35 Remark.** A morphism $\pi: X \rightarrow Y$ has the right lifting property against all morphisms in $I^\partial$ if its image by the forgetful functor to $\infty$-$\mathbf{Cat}$ is an acyclic fibration; that is, if for every pair of parallel $n$-arrows $u, v$ in $X$, the map $\operatorname{Hom}_X(u, v) \rightarrow \operatorname{Hom}_Y(\pi(u), \pi(v))$ is surjective.

$\pi$ has the right lifting property against all morphisms in $I^{+m}$ if and only if for every arrow $f \in X$ such that $\pi(f)$ is marked in $Y$, $f$ is marked in $X$. An acyclic fibration is a map that has both these properties.

The pushout-product, or corner-product (sometimes also called the Leibniz product) $f \bar{\ominus} g$ and $f \bar{\ominus} g$ is defined as usual: if $f: X \rightarrow Y$ and $g: A \rightarrow B$ are two morphisms in $\infty$-$\mathbf{Cat}^{+m}$, then $f \bar{\ominus} g$ is the canonical morphism:

$$X \ominus B \coprod_{X \ominus A} Y \ominus A \rightarrow Y \ominus B$$

17