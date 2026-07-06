We can now conclude the proof of this implication with:

**2.4 Lemma.** *Any category I satisfying conditions (L1) or (L2) of Theorem 1.2 is essentially $\kappa$-small.*

*Proof.* We have seen in Lemma 2.3 that $I$ is locally $\kappa$-small. $I$ also satisfies the last (hence all) condition of Proposition 2.1. Hence the functor $\operatorname{Hom}: I^{\mathrm{op}} \times I \to \mathbf{Sets}$ is $\kappa$-presentable. In general, given a $\kappa$-presentable object $X$ of a functor category $\mathbf{Sets}^K$, one can show that there is a $\kappa$-small family of elements $a_x \in X(k_x)$ such that every element of $X$ is the image of one of $a_x$ by the functoriality of $X$. Indeed each such family defines a subobject of $X$ and together they form a $\kappa$-filtered family of subobjects of $X$, so if $X$ is $\kappa$-presentable, then one of these subobjects is equal to $X$.

In our case, it means that there exists a $\kappa$-small set of arrows $f_x: a_x \to b_x \in I$ for $x \in X$ such that every arrow $g$ of $I$ can be factored through one of these as $g = u f_x v$ for some $x \in X$. In particular, for each object $y \in I$, we have two arrows $u, v$ such that $Id_y = u f_x v$, which implies that $y$ is a retract of $a_x$ (as well as of $b_x$). The category $I$ being locally $\kappa$-small, the full subcategory of the $a_x$ is a $\kappa$-small category $A$ and we just showed that $I$ identifies with a full subcategory of the Cauchy completion of $A$, hence is an essentially $\kappa$-small category, as the Cauchy completion of a $\kappa$-small category can be constructed as a $\kappa$-small category. $\square$

## 2.2 Proof of (L3) $\Rightarrow$ (L1)

We fix $A$ a locally $\kappa$-presentable category and $I$ a $\kappa$-small category. We will show condition (L1), i.e. that $A^I$ is also locally $\kappa$-presentable with its $\kappa$-presentable objects being the functors taking values in the full subcategory $A_\kappa$ of $\kappa$-presentable objects of $A$. Note that by Proposition 2.1, as $I$ is $\kappa$-small, the functors $I \to A_\kappa$ are indeed $\kappa$-presentable objects of $A^I$.

The evaluation functor $ev_i: A^I \to A$ (for $i \in I$) have left adjoints $F_i: A \to A^I$ than can be expressed as

$$F_i(X) := \left( j \mapsto \coprod_{\operatorname{Hom}_I(i,j)} X \right) \in A^I.$$

In particular, as the category $I$ is $\kappa$-small this coproduct is $\kappa$-small and hence if $X \in A_\kappa$, then $F_i(X) \in (A_\kappa)^I$. We have that for any $U \in A^I$, $\operatorname{Hom}(F_i(X), U) = \operatorname{Hom}(X, ev_i(U))$, so it follows that an arrow $f: U \to V$ in $A^I$ is an isomorphism if and only if for each $X \in A_\kappa$ and each $i \in I$ we have that

$$\operatorname{Hom}(F_i(X), U) \to \operatorname{Hom}(F_i(X), V)$$

is an equivalence. The following lemma, applied to the cocomplete category $\mathcal{A}^I$ and to $\mathcal{C} = (\mathcal{A}_\kappa)^I$ then concludes the proof:

**2.5 Lemma.** *Let $\mathcal{A}$ be a cocomplete category and let $\mathcal{C} \subset \mathcal{A}$ be a full subcategory of $\mathcal{A}$ such that:*

(1) \(\mathcal{C}\) is closed under \(\kappa\)-small colimits in \(\mathcal{A}\).
(2) Every object of \(\mathcal{C}\) is \(\kappa\)-presentable in \(\mathcal{A}\).

7