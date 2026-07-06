(W3) $\Rightarrow$ (W4) is tautological.

(W4) $\Rightarrow$ (W5). The construction $I^{(\text{Ord})}$ is not a functor in the 2-categorical or bicategorical sense, but it is functorial in the 1-categorical sense nonetheless. So given an equivalence $F: A \rightarrow I$ with $A$ a strictly well-founded category, we get a commutative square:

$$\begin{array}{ccc} A^{(\text{Ord})} & \xrightarrow{F^{(\text{Ord})}} & I^{(\text{Ord})} \\ \downarrow{\pi_A} & & \downarrow{\pi_I} \\ A & \xrightarrow{F} & I \end{array}$$

By point (SW5) of Proposition 3.3, the left functor $\pi_A$ has a section $s$ (up to equality) and the bottom functor $F$ is an equivalence (so it has an inverse up to is morphisms), so composing $F^{(\text{Ord})}sF^{-1}$ gives a functor $I \rightarrow I^{(\alpha)}$ such that if one post-compose it by $\pi_I$ we get $\pi_I F^{(\text{Ord})}sF^{-1} = F\pi_A sF^{-1} = FF^{-1} \simeq \text{Id}_I$ hence the result.

(W5) $\Rightarrow$ (W6) is tautological.

(W6) $\Rightarrow$ (W1). We get a functor $F: I \rightarrow \text{Ord}$ by composing the functor $I \rightarrow I^{(\text{Ord})}$ with the projection $I^{(\text{Ord})} \subset I \times \text{Ord} \rightarrow \text{Ord}$. Let $f$ be any arrow such that $F(f)$ is an identity. As the only arrows in $I^{(\text{Ord})}$ sent to identities in $\text{Ord}$ are identities, it follows that the image of $f$ is already an identity arrow in $I^{\text{Ord}}$, hence $f$ is a retract of an identity arrow in $I$, so it has to be an isomorphism. This proves that the functor to $\text{Ord}$ is conservative. If we further assume that $f$ is an endomorphism of an object, then the same argument shows that $f$ is a retract of an identity, with the same retraction on each side, which forces $f$ to be an identity arrow, hence this concludes the proof. $\square$

### 3.2 Proof of (A2) $\Rightarrow$ (A4)

We fix $I$ a category such that for all Cauchy complete category $\mathcal{C}$, the functor $E_{\mathcal{C},\kappa}^I: \text{Ind}_\kappa(\mathcal{C}^I) \rightarrow \text{Ind}_\kappa(\mathcal{C})^I$ is an equivalence. It is in particular an equivalence for all category $\mathcal{C}$ having $\kappa$-small colimits, so by Theorem 1.2 the category $I$ is $\kappa$-small.

We then take $\mathcal{C} = I^{(\kappa)}$. For each $x \in I$, we consider the object $E_x \in \text{Ind}_\kappa$ defined as follows:

$$E_x = \underset{\alpha < \kappa}{\text{Colim}}(x, \alpha)$$

As $\kappa$ is assumed to be a regular cardinal (which we consider as an ordinal here), the poset $\kappa$ has all $\kappa$-small join and hence is $\kappa$-directed. As a functor $\mathcal{C}^{\text{op}} \rightarrow \text{Sets}$, $E_x$ can be described as:

$$E_x(y, \alpha) = \text{Hom}_I(y, x)$$

So this clearly constitutes a functor $E: I \rightarrow \text{Ind}_\kappa(\mathcal{C})$. It should also be noted that the functor $\text{Ind}_\kappa(\pi_I): \text{Ind}_\kappa(I^{(\alpha)}) \rightarrow \text{Ind}_\kappa(I)$ sends the objects $E_x$ to the object $x$ itself as the all the $(x, \alpha)$ are sent to $x$ and hence the colimit defining $E_x$ becomes trivial in $\text{Ind}_\kappa(I)$. So that the composite $\text{Ind}_\kappa(\pi_I) \circ E: I \rightarrow \text{Ind}_\kappa(I)$ identifies with the canonical functor $I \rightarrow \text{Ind}_\kappa(I)$.

As we are assuming condition (A2) of Theorem 1.3 and the category $\mathcal{C} = I^{(\kappa)}$ is Cauchy complete (it has no non-identity idempotent), we can hence find a

11