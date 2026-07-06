both cases a key observation is that as the result is assumed to be true for $\beta$, both these claims are true when $\beta$ is replaced by $\alpha$.

So we consider a $\kappa$-small diagram $X^i \rightarrow Y$ in $\mathcal{C}^{I^{(\alpha)}}/Y$ and we will show it admits a cocone. First, by our induction hypothesis, the restriction to $I^{(\beta)}$ has a cocone $X^i|_{I^{(\beta)}} \rightarrow E \rightarrow Y|_{I^{(\beta)}}$. We only need to extend $E$ to the object of the form $(\alpha, i) \in I^{(\alpha)}$, endowed with maps $E(\alpha, i) \rightarrow Y(\alpha, i)$, and all the appropriate maps from the $E(\beta, i) \rightarrow E(\alpha, i)$ and maps $X^i(\alpha, i) \rightarrow E(\alpha, i)$ such that composites, for example $E(\beta, i) \rightarrow E(\alpha, i) \rightarrow Y(\alpha, i)$, are the correct maps. This can be summed up as the question of finding a cocone for a certain $\kappa$-small diagram in $\mathcal{C}/Y(\alpha, i)$, hence we can build these objects as $Y(\alpha, i) \in \text{Ind}_\kappa(\mathcal{C})$.

Finally, similarly to the proof of Proposition 3.5, in order to show that $Y$ is the colimits of $\mathcal{C}^{I^{(\alpha)}}/Y$, it is enough to show that for all $\gamma \leqslant \alpha$ and for each arrow $V \rightarrow Y(\gamma, i)$ for $V \in \mathcal{C}$, this arrow can be factored as $V \rightarrow X(\gamma, i) \rightarrow Y(\gamma, i)$ for $X \in \mathcal{C}^I/Y$, and that any two such factorizations are equalized by some $X \rightarrow X'$ in $\mathcal{C}^I/Y$. But this is easily done by the exact same argument: One first builds the restriction of $X$ to $I^{(\beta)}$ by the induction hypothesis and then we extend $X$ to $I^{(\alpha)}$ by finding certain cocones for $\kappa$-small diagrams in $\mathcal{C}/Y(\alpha, i)$.

We now move to that last part of the proof: $\alpha$ is a limit ordinal, then $I^{(\alpha)}$ is the union of the $I^{(\beta)}$ for $\beta \subset \alpha$, which are all sieve in $I^{(\alpha)}$. Hence

$$\mathcal{C}^{I^{(\alpha)}} = \lim_{\beta < \alpha} \mathcal{C}^{I^{(\beta)}}$$

and Lemma 3.7 immediately implies that this limit satisfies the conditions of Proposition 3.5, hence:

$$\text{Ind}_\kappa(\mathcal{C}^{I^{(\alpha)}}) \simeq \lim_{\beta < \alpha} \text{Ind}_\kappa(\mathcal{C}^{I^{(\beta)}})$$

hence by our induction hypothesis, we obtain

$$\text{Ind}_\kappa(\mathcal{C}^{I^{(\alpha)}}) \simeq \lim_{\beta < \alpha} \text{Ind}_\kappa(\mathcal{C})^{I^{(\beta)}} \simeq \text{Ind}_\kappa(\mathcal{C})^{I^{(\alpha)}},$$

which concludes the proof.

We can now prove the claimed implication:

**3.9 Proposition.** *Let $I$ be an essentially $\kappa$-small well-founded category, and $\mathcal{C}$ any category, then*

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(\mathcal{C}^I) \rightarrow \text{Ind}_\kappa(\mathcal{C})^I$$

*is an equivalence of categories.*

*Proof.* One can freely assume that $I$ is $\kappa$-small. As $I$ is well-founded, then the projection $I^{(\text{Ord})} \rightarrow I$ admits a section up to isomorphism. The composite functor $I \rightarrow I^{(\text{Ord})} \rightarrow \text{Ord}$ has a $\kappa$-small image, so it factors through an order preserving inclusion $\alpha \subset \text{Ord}$ for $\alpha$ a $\kappa$-small ordinal.

The full subcategory of objects of $I^{(\text{Ord})}$ whose image in $\text{Ord}$ is in this $\kappa$-small ordinal identifies to $I^{(\alpha)}$, and hence we have a section (up to isomorphic) of the projection $I^{(\alpha)} \rightarrow I$.

It follows that the functor $E_{\mathcal{C},\kappa}^I$ is a retract (up to natural isomorphisms) of the functor $E_{\mathcal{C},\kappa}^{I^{(\alpha)}}$, which is known to be an equivalence by Proposition 3.8, hence is itself an equivalence of category.

15