**Theorem 6.7.** *Let $\mathcal{E}$ be a $\lambda$-presentable category and let $\mathcal{A}$ be the full subcategory of $\lambda$-presentable objects. Then for a monad $M \in \mathbf{Mnd}_{\mathcal{E}}$ the following conditions are equivalent:*

1. $M$ is $\lambda$-accessible.
2. $M$ has arities in $\mathcal{A}$.
3. $M$ is $\mathcal{A}$-nervous.

*Proof.* $1 \Rightarrow 2$: If $M$ is $\lambda$-accessible then $M$ preserves all $\lambda$-directed colimits. Because all objects in $\mathcal{A}$ are $\lambda$-compact, the restricted Yoneda embedding $\mathcal{E} \rightarrow \Pr(\mathcal{A})$ preserves $\lambda$-directed colimits. Since for each $X \in \mathcal{E}$ the category $X_{/\mathcal{A}}$ is $\lambda$-directed (it has $\lambda$-small colimits) this concludes the proof.

$2 \Rightarrow 3$ is Theorem 6.4.

$3 \Rightarrow 1$: $M$ being $\mathcal{A}$-nervous means that the square:

$$\begin{array}{ccc} \mathcal{E}^M & \longrightarrow & \Pr(\text{Th}_{\mathcal{A}}(M)) \\ \downarrow & & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

is a pullback square. Now the right vertical functor preserves all colimits (in particular, $\lambda$-directed ones), and the bottom horizontal functor preserves $\lambda$-directed colimits as mentioned above. It hence follows that all functors in the diagram preserve $\lambda$-directed colimits by 3.24. The underlying functor of the monad $M$ identifies with the composite of the forgetful functor $\mathcal{E}^M \rightarrow \mathcal{E}$ and its left adjoint (which automatically preserves colimits), so it preserves $\lambda$-directed colimits. Thus, $M$ is $\lambda$-accessible. $\square$

**Corollary 6.8.** *Let $M$ be a $\lambda$-accessible monad on a $\lambda$-presentable $\infty$-category $\mathcal{E}$. Then the $\infty$-category $\mathcal{E}^M$ of $M$-algebra is locally presentable. In particular it has all colimits.*

*Proof.* With $\mathcal{A}$ the full subcategory of $\lambda$-presentable objects, we have by Theorem 6.7 pullback diagram:

$$\begin{array}{ccc} \mathcal{E}^M & \longrightarrow & \Pr(\text{Th}_{\mathcal{A}}(M)) \\ \downarrow & & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

41