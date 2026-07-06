*Remark 2.39.* There is also a more general notion called “weak Quillen functors” introduced in [Hen20] which is sometimes more convenient. The functor $L$ is only defined on cofibrant objects and $R$ on fibrant objects, and they are only required to preserve core (co)fibrations – all results in this section below, as well as the $4^{th}$ invariance theorem from section 4 apply to weak Quillen adjunctions too. We restrict ourselves to Quillen adjunctions in the paper, unless otherwise stated, for simplicity, and because this already cover most of the applications.

**Construction 2.40.** Given a Quillen adjunction$^2$ $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$. Then, $L$ restricts to a coclan morphism $L : \mathcal{C}^{\text{COF}} \rightarrow \mathcal{D}^{\text{COF}}$, which following theorem 2.29 we have a (unique) comparison map

$$\alpha_L : \mathbb{L}^\mathcal{C}_\lambda \rightarrow L^* \mathbb{L}^\mathcal{D}_\lambda$$

obtained from the fact that $\mathbb{L}^\mathcal{C}_\lambda$ is an initial boolean algebra over $\mathcal{C}$. As before, if $\phi \in \mathbb{L}^\mathcal{C}_\lambda(C)$, we often write $L(\phi)$ instead of $\alpha_L(\Phi)$. Note that $L(\phi) \in \mathbb{L}^\mathcal{D}_\lambda(L(C))$.

Finally, exactly as in theorem 2.29, we have:

**Proposition 2.41.** *For a Quillen adjunction $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$, any$^3$ object $X \in \mathcal{D}$, and cofibrant object $C \in \mathcal{C}$, any map $v : C \rightarrow R(X)$ corresponding to $\tilde{v} : LC \rightarrow X$, and $\phi \in \mathbb{L}^\mathcal{C}_\lambda$ we have*

$$R(X) \vdash \phi(v) \Leftrightarrow X \vdash L(\phi)(\tilde{v}).$$

*Proof.* See theorem 2.29. $\square$

The $4^{th}$ invariance theorem that we will establish in section 4 as theorem 4.2 shows that for a Quillen equivalence, this construction gives an equivalence between the language of $\mathcal{C}$ and of $\mathcal{D}$ in an appropriate sense.

### 3 Examples of languages of model categories

In this section, we examine some examples of the language associated to a model category by applying the construction as described in section 2. We include examples we believe to be of interest. Furthermore, we start with some general considerations that allow us to construct the language of a model category.

$^2$Or more generally a weak Quillen adjunction in the sense of [Hen20].

$^3$If $L$ and $R$ are only a weak Quillen adjunction, then $X$ needs to be fibrant.

29