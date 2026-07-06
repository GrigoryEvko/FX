Hence in Theorem 1.2, condition (L1) could be rephrased as simply: the $\kappa$-presentable objects of $A^I$ are exactly the functor $I \to A_\kappa$.

Finally, after the publication of a first preprint version of the present paper, Leonid Positelski published a result that significantly improved some aspect of our Theorem 1.2 by showing the requirement that the category $A$ is locally presentable can be considerably weakened, without automatically falling under the scope of Theorem 1.3. More precisely, theorem 6.1 of [12] assert that:

**1.5 Theorem** (Positelski [12]). *Let $\kappa$ be a regular cardinal and $\lambda < \kappa$ another infinite cardinal. If $I$ is a $\kappa$-small category and $A$ is a $\kappa$-accessible category which has colimits of $\lambda$-indexed chains, then the category $A^I$ is $\kappa$-accessible and its $\kappa$-presentable objects are the functor $I \to A_\kappa$.*

In particular, using this and Proposition 1.1, we obtain that $\text{Ind}_\kappa(C^I) \simeq \text{Ind}_\kappa(C)^I$ when $I$ is $\kappa$-small and $C$ is Cauchy complete with colimits of $\lambda$-chain for $\lambda < \kappa$ an infinite cardinal.

Note that [12] also proves similar results for more general weighted limits of accessible categories. This result also immediately gives a very good upper bound on the accessibility rank of $A^I$ in general:

**1.6 Corollary** (Positelski). *Let $\kappa$ be a regular cardinal, $I$ a $\kappa$-small category, $A$ a $\kappa$-accessible category and $\lambda$ any regular cardinal such that $\kappa \triangleleft \lambda$. Then $A^I$ is $\lambda$-accessible and its $\lambda$-presentable objects are the functors $I \to A_\lambda$.*

Where $\kappa \triangleleft \lambda$ is the “sharply less” relation from [1, Definition 2.12]. This applies for example of $\lambda = \kappa^+$ is the successor cardinal of $\kappa$.

*Proof.* Under the condition $\kappa \triangleleft \lambda$, the category $A$ is also $\lambda$-accessible and has $\kappa$-directed colimits. In particular it has colimits of chain indexed by $\kappa$ for $\kappa < \lambda$ an infinite cardinal, so we can apply Theorem 1.5 and concludes. $\square$

This paper arose following a discussion on Mathoverflow [6]. In particular, I am especially grateful to Ben Wieland for suggesting a first counter example to the claim that $E_{\omega,\mathcal{C}}^I$ is an equivalence when $I$ is $\omega$-small, which was the starting point to the proof in subsection 3.2, and to Ivan Di Liberti for pointing me to Makkai’s theorem 5.1 in [10].

## 2 Proof of Theorem 1.2.

The equivalence of conditions (L1) and (L2) of Theorem 1.2 follows immediately from Proposition 1.1 and the fact that a $\kappa$-accessible category is locally presentable if and only if its $\kappa$-presentable objects have $\kappa$-small colimits. So we only need to show the equivalence with condition (L3).

We start by observing the following equivalences:

**2.1 Proposition.** *Let $I$ be a category. The following conditions are equivalents:*

(1) *The functor*

$$\text{Hom}(\_\_\_\_\_) : I^{\text{op}} \times I \to \mathbf{Sets}$$

*is a $\kappa$-presentable object of $\mathbf{Sets}^{I^{\text{op}} \times I}$.*

4