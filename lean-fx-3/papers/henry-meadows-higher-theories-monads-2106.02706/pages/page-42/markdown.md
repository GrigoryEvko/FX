$\Pr(M^\lambda), \Pr(C^\lambda)$ are locally presentable by [15, Theorem 5.5.1.1]. The vertical right map preserve all limits and all colimits so it is an accessible right adjoint functor and the bottom horizontal map preserves all limits and $\lambda$-directed colimits, so it is also an accessible right adjoint. It then follows from [15, Theorem 5.5.3.18] that taking this pullback in the category of presentable categories and right adjoint functors between them gives the same results, and hence $\mathcal{E}^M$ is itself locally presentable. $\square$

**Corollary 6.9.** *Let $\mathcal{E}$ be a locally presentable category and $M: I \rightarrow \mathbf{Mnd}_{\mathcal{E}}$ a diagram such that $M(i)$ is accessible for each $i \in I$, then $M$ has a colimit in $\mathbf{Mnd}_{\mathcal{E}}$ and the natural map:*

$$\mathcal{E}^{\text{Colim } M_i} \rightarrow \lim_{i \in I} \mathcal{E}^{M_i}$$

*is an equivalence of $\infty$-categories.*

More precisely, the proof will show that if $\mathcal{E}$ is $\kappa$-presentable and all $M(i)$ are $\kappa$-accessible then the colimit is $\kappa$-accessible.

*Proof.* Given $\kappa$ a regular cardinal such that $\mathcal{E}$ is $\kappa$-presentable and all $M(i)$ are $\kappa$-accessible, Theorem 6.7 shows that all $M(i)$ are $\mathcal{A}$-nervous for $\mathcal{A}$ the category of $\kappa$-compact objects in $\mathcal{A}$, and Theorem 6.3 implies the result. $\square$

## 7 Monads as Kleisli categories

The goal of this section is to show that one can works with a monad purely in terms of its Kleisli category, so that defining a monad on $\mathcal{C}$ is the same as defining a bijective on objects left adjoint functor $\mathcal{C} \rightarrow \mathcal{K}$. This section is generally independent of the rest of the paper, but uses very similar methods and fits in the general goal of providing tools to work more easily with monads on $\infty$-categories.

**Definition 7.1.** Let $\mathbf{LAdj}_{\mathcal{C}}$ be the full subcategory of $(\mathbf{Cat}_{\infty})_{\mathcal{C}/}$ on *left adjoint essentially surjective functors*.

Let $\text{Kl}: \mathbf{Mnd}_{\mathcal{C}} \rightarrow \mathbf{LAdj}_{\mathcal{C}}$ be the Kleisli category construction. The main result of this section is:

**Theorem 7.2.** *The functor $\text{Kl}$ is an equivalence of $\infty$-categories between the $\infty$-categories $\mathbf{Mnd}_{\mathcal{C}}$ and $\mathbf{LAdj}_{\mathcal{C}}$.*

42