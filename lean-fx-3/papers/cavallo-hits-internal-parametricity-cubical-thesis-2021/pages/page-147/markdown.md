Kan operations 135

We define $Pcoe^\nu$ to be the greatest fixed-point of $Pcoe^{-1}$, which is a $\Psi$-PER by virtue of Lemma 6.3.6.

We quickly see that not only values but terms in $Pcoe^{-1}$ are coercible.

**Lemma 6.3.8 (Parameter coercion from $Pcoe^{-1}$).** Any $(\Psi, \Delta)$-PER $R$ validates the following rules for all $\Psi', x : \mathbb{I} \Vdash \psi \in \Psi, \Psi' \Vdash r, s \in \mathbb{I}$, and $\Psi' \Vdash \delta \in \Delta\psi[r/x]$.

$$\frac{M \approx M' \in \Downarrow Pcoe^{-1}(R)[\psi[r/x], \delta]}{\mathsf{pcoe}_{x.\Delta\psi \blacktriangleright x.\mathcal{K}\psi}^r(M) \approx \mathsf{pcoe}_{x.\Delta'\psi \blacktriangleright x.\mathcal{K}'\psi}^r(M') \in \Downarrow R[\psi[s/x], \overline{\mathsf{coe}}_{x.\Delta\psi}^r(\delta)]}$$
$$\frac{M \in \Downarrow Pcoe^{-1}(R)(\psi[r/x], \delta)}{\mathsf{pcoe}_{x.\Delta\psi \blacktriangleright x.\mathcal{K}\psi}^r(M) \approx M \in \Downarrow R[\psi[r/x], \delta]}$$

*Proof.* We apply our elimination lemma, Lemma 3.1.38. Here we use that $Pcoe^{-1}(R) \subseteq [\mathsf{Ind}_{\mathcal{K}}^\Delta(-)]$ by definition. It then suffices to check that these rules hold when the input terms are values in $Pcoe^{-1}(R)[\psi[r/x], \delta]$, in which case the conclusions are also true by definition of $Pcoe^{-1}(R)$. $\square$

We now show that $Pcoe^\nu$ is closed under the individual introduction form relations making up $Step^{\mathcal{K}}$: $Fcoe$, $Fhcom$, and $Intro_\ell^{\mathcal{K}}$ for $\ell \in \mathcal{K}$. In each case, we first show that parameter coercion applied to the introduction form can be reduced to some application of introduction forms to coercions of the arguments.

**Lemma 6.3.9 (Reduction of pcoe on fcoe).** The following holds for any $(\Psi, \Delta)$-PER $R$, substitution $\Psi', x : \mathbb{I} \Vdash \psi \in \Psi, \Psi' \Vdash r, s \in \mathbb{I}$, and $\Psi', y : \mathbb{I} \Vdash \delta \in \Delta\psi[r/x]$.

$$\frac{\Psi' \Vdash t, u \in \mathbb{I} \qquad M \in \Downarrow Pcoe^{-1}(R)[\psi[r/x], \delta[t/y]]}{\mathsf{pcoe}_{x.\mathcal{K}\psi \blacktriangleright x.\Delta\psi}^r(\mathsf{fcoe}_{y.\delta}^{t\to u}(M))}$$
$$\approx$$
$$\mathsf{fcoe}_{y.\mathsf{coe}_{x.\Delta}^{t\to u}(\delta)}^{\tau\to u}(\mathsf{pcoe}_{x.\Delta \blacktriangleright x.\mathcal{K}}^{r\to s}(M))$$
$$\in$$
$$\Downarrow Fcoe?(R)[\psi[s/x], \overline{\mathsf{coe}}_{x.\Delta\psi}^{r\to s}(\delta[u/y])]$$

*Proof.* By coherent head expansion. Let $\Psi'' \Vdash \psi' \in \Psi'$ be given. We are in one of two cases. If $t\psi' = u\psi'$, then we have $\mathsf{pcoe}_{x.\mathcal{K}\psi \blacktriangleright x.\Delta\psi}^{r\to s}(\mathsf{fcoe}_{y.\delta}^{t\to u}(M))\psi \longmapsto \mathsf{pcoe}_{x.\mathcal{K}\psi \blacktriangleright x.\Delta\psi}^{r\to s}(M)\psi$, and the reduct is related to our right side by Lemmas 6.3.8 and 6.2.14. If $t\psi' = u\psi'$, then the left side reduces to the right side, which is again in the relation by Lemmas 6.3.8 and 6.2.14. $\square$

**Corollary 6.3.10.** For any $(\Psi, \Delta)$-PER $R$, we have $Fcoe(Pcoe^{-1}(R)) \subseteq Pcoe^{-1}(Fcoe?(R))$.