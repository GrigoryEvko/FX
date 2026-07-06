(L3) $I$ is essentially $\kappa$-small (that is equivalent to a $\kappa$-small category).

# **1.3 Theorem.** For a category $I$ the following conditions are equivalent:

(A1) For every category $\mathcal{C}$ the functor

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(C^I) \rightarrow \text{Ind}_\kappa(C)^I$$

is an equivalence.

(A2) For every Cauchy complete category $\mathcal{C}$, the functor $E_{\mathcal{C},\kappa}^I$ above is an equivalence.

(A3) For any $\kappa$-accessible category $A$, the category $A^I$ is $\kappa$-accessible and its $\kappa$-presentable objects are the functor $I \rightarrow A_\kappa$.

(A4) $I$ is essentially $\kappa$-small and well-founded in the sense of Proposition 3.4.

We refer the reader to Proposition 3.3 and Proposition 3.4 for various equivalent definitions of well-founded categories, but one of these characterizations is that $I$ has no non-trivial endomorphisms and that its posetal reflection is a well-founded poset. In particular, in the case of $\kappa = \omega$, condition (A4) means that $I$ is equivalent to a finite category with no non-identity endomorphisms. That fact that $\text{Ind}(C^I) = \text{Ind}(C)^I$ for such category was already proved as Proposition 8.8.5 of exposé I of [4], as well as in C.Meyer PhD Thesis (page 55) [11]. So in this case, our contribution is only to show that this condition is necessary.

Similarly, Proposition 5.3.5.15 from [9] shows in the framework of $\infty$-categories that $E_{\mathcal{C},\kappa}^I$ is an equivalence for any regular cardinal $\kappa$ and any $\infty$-category $\mathcal{C}$ when $I$ is a finite poset. This result can be applied as is to 1-categories, so it does recover a special case of our Theorem 1.3, this time beyond the case $\omega = \kappa$, but with less general conditions on the category $I$.

For an explicit counter-example to Makkai's theorem, the reader should go to Section 3.2, where we show, using an explicit construction, that point (A2), or equivalently (A3), implies point (A4) in Theorem 1.3. In particular, for any $\kappa$-small category $I$ which is *not* well-founded, we will build a category $C = I^{(\kappa)}$ (see Construction 3.1) so that the accessible category $A = \text{Ind}_\kappa(C)$, is such that not every functor in $A^I$ is a $\kappa$-filtered colimit of functors $I \rightarrow A_\kappa$ (here $C = A_\kappa$ because $C = I^{(\kappa)}$ will be Cauchy-complete).

It should be noted that the requirement in conditions (A3) and (L1) that the $\kappa$-presentable objects of $A^I$ are the functors $I \rightarrow A^\kappa$ is absolutely essential to both theorems. For example, in the case of locally presentable categories, we have

# **1.4 Theorem.** Let $\mathcal{C}$ be a locally $\kappa$-presentable category, and $I$ be any small category. Then the category of functors $\mathcal{C}^I$ is locally $\kappa$-presentable.

*Proof.* This follows from Theorem 2.17 of G. Bird PhD thesis [2], which claims that the bicategory of locally $\kappa$-presentable category and $\kappa$-accessible right adjoint functors between them has all **Cat**-enriched pseudo limits and they are preserved by the forgetful functor to **Cat**. The functor category $\mathcal{C}^I$ corresponds to the co-tensor for the locally $\kappa$-presentable category $\mathcal{C}$ by the category $I$. $\square$

3