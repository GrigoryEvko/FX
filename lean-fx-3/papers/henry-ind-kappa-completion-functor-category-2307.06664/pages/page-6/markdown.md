We also mention the following corollary of Proposition 2.1, which will be useful in the proof of Theorem 1.3 later, and is also interesting in its own right. This is directly inspired by proposition 8.8.2 of [4].

**2.2 Corollary.** *Let $I$ be an essentially $\kappa$-small category, or more generally a category satisfying the equivalent conditions of Proposition 2.1, then the functor*

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(C^I) \rightarrow \text{Ind}_\kappa(C)^I$$

*is fully faithful.*

*Proof.* Let $X$ and $Y$ be two objects of $\text{Ind}_\kappa(C^I)$, we write them as $\kappa$-directed colimits, $X = \text{Colim } X_i$ and $Y = \text{Colim } Y_j$ of diagrams in $C^I$. In the category $\text{Ind}_\kappa(C^I)$ we have

$$\begin{aligned} \text{Hom}(X, Y) &= \text{Hom}(\underset{i}{\text{Colim }} X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \text{Hom}(X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \underset{j}{\text{Colim}} \text{Hom}(X_i, Y_j) \end{aligned}$$

as the $X_i$ are $\kappa$-presentable in $\text{Ind}_\kappa(C^I)$. In the category $\text{Ind}_\kappa(C)^I$ we have

$$\begin{aligned} \text{Hom}(E_{\mathcal{C},\kappa}^I(X), E_{\mathcal{C},\kappa}^I(Y)) &= \text{Hom}(\underset{i}{\text{Colim }} E_{\mathcal{C},\kappa}^I(X_i), \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \text{Hom}(X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \underset{j}{\text{Colim}} \text{Hom}(X_i, Y_j) \end{aligned}$$

where we have used that the functor $E$ preserves $\kappa$-directed colimits by construction, and that by Proposition 2.1 the $X_i \in C^I$ are $\kappa$-presentable objects in $\text{Ind}_\kappa(C)^I$. This concludes the proof as one easily see by functoriality of the isomorphisms above that the identification $\text{Hom}(X, Y) = \text{Hom}(E_{\mathcal{C},\kappa}^I(X), E_{\mathcal{C},\kappa}^I(Y))$ we obtained is induced by the action of $E_{\mathcal{C},\kappa}^I$. $\square$

## 2.1 Proof of (L1) or (L2) $\Rightarrow$ (L3)

We fix $I$ for which the equivalent conditions (L1) and (L2) of Theorem 1.2 holds. We will show that $I$ is $\kappa$-small. We first have

**2.3 Lemma.** *Any category $I$ satisfying conditions (L1) or (L2) of Theorem 1.2 is locally $\kappa$-small, that is has $\kappa$-small Hom sets.*

*Proof.* We apply condition (L1) to the category **Sets**, whose $\kappa$-presentable objects are the $\kappa$-small sets. It follows that for every $x \in I$ the representable functor

$$\begin{aligned} I &\rightarrow \quad \textbf{Sets} \\ y &\mapsto \quad \text{Hom}(x, y) \end{aligned}$$

can be written as a $\kappa$-filtered colimit of functors $I \rightarrow \textbf{Sets}_\kappa$. In particular, there exists a functor $A : I \rightarrow \textbf{Sets}_\kappa$ and a natural transformation $\lambda_y : A(y) \rightarrow \text{Hom}(x, y)$, such that the identity functor $x \rightarrow x$ can be written as $\lambda_x(e)$ for $e \in A(x)$. But it then follows that for every arrow $p : x \rightarrow y$, we have $\lambda_y(pe) = p\lambda_y(e) = p \circ \text{Id}_x = p$, hence $A(y) \rightarrow \text{Hom}(x, y)$ is surjective, and hence $\text{Hom}(x, y)$ is a $\kappa$-small set for all $x, y \in I$. $\square$

6