138

General higher inductive types

Proof. We first check that the right side is well-typed, beginning by verifying that each of the auxiliary terms is well-typed.

- $\Psi', x : \mathbb{I} \Vdash \omega^x \in \Omega\phi$ and $\Psi' \Vdash \omega^r = \omega \in \Omega[r/x]\phi$ by Lemma 6.3.2.
- $\chi^x \in \Downarrow \{\Theta^x\}_{\mathcal{K}}(Pcoe^\nu\psi)$ and $\chi^r \approx \chi \in \Downarrow \{\Theta^r\}_{\mathcal{K}}(Pcoe^\nu\psi[r/x])$, where $\Theta^x = \Theta[\phi, \omega^x]$, by the above properties of $\omega^x$ and Lemmas 6.3.17 and 6.3.18.
- $\Psi', x : \mathbb{I} \Vdash \delta^x \in \Delta\psi$ and $\Psi', x : \mathbb{I} \Vdash \delta^s = \delta[s/x]\omega^s \in \Delta\psi[s/x]$ by Lemma 6.3.2.
- $M_i^x \approx M_j^x \in \Downarrow Pcoe^\nu[\psi, \delta^x]$ for all $i, j$ by the above and Lemmas 6.2.19 and 6.3.8.

From the first three of these instantiated at $[s/x]$ and Lemma 6.2.18, we can conclude that $\text{intro}_{\ell}^{\mathcal{K}\psi[s/x]}(\phi; \omega^s; \chi^s) \in \Downarrow \text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu)[\psi, \delta^s]$. Said lemma moreover gives us the following boundary equation for each $i$.

$$\Psi', \xi_i \gg \text{intro}_{\ell}^{\mathcal{K}\psi[s/x]}(\phi; \omega^s; \chi^s) \approx M_i^s \in \Downarrow \text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu)[\psi, \delta^s]$$

It then follows from Lemmas 6.2.14 and 6.2.15, combined with Corollaries 6.3.11 and 6.3.14, that the right side is in $\Downarrow Fcom?(Intro_{\ell}^{\mathcal{K}}?(Pcoe^\nu))[\psi[s/x], \overline{\text{coe}}_{x,\Delta\psi}^{r\to s}(\delta)]$. Moreover, under the assumption of some constraint $\xi_i$, it is related to $M_i^r$, which is in turn related to $\text{pcoe}_{x,\Delta\psi \blacktriangleright x,\mathcal{K}\psi}^{r\to s}(\langle \Theta.M_k[r/x][\phi, \omega] \rangle_{\mathcal{K}'}(\chi))$ by the above.

We proceed with a standard argument by coherent head expansion. Under any substitution $\Psi'' \Vdash \psi' \in \Psi'$, either some $\xi_k\psi'$ holds for a minimal $k$ or there is no such $k$. In the latter case, the left side reduces to the right side. In the former case, it reduces to $\text{pcoe}_{x,\Delta\psi \blacktriangleright x,\mathcal{K}\psi}^{r\to s}(\langle \Theta.M_k[r/x][\phi, \omega] \rangle_{\mathcal{K}'}(\chi))$, which we have just seen is equal to the right side in that circumstance.

Corollary 6.3.20. For any $\ell \in \mathcal{K}$ such that $\text{Intro}_{\ell'}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^\nu$ for every $\ell'$ with $|\ell'|_{\mathcal{K}} < |\ell|_{\mathcal{K}}$, we have $\text{Intro}_{\ell}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^{-1}(Fcom?(Intro_{\ell}^{\mathcal{K}}?(Pcoe^\nu)))$.

Proof. As with Corollaries 6.3.10 and 6.3.13.

Lemma 6.3.21. We have $\text{Intro}_{\ell}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^\nu$ for all $\ell \in \mathcal{K}$.

Proof. By strong induction on the height of $\ell$ in $\mathcal{K}$. Suppose that $\text{Intro}_{\ell'}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^\nu$ for every $\ell'$ with $|\ell'|_{\mathcal{K}} < |\ell|_{\mathcal{K}}$.

Rather than showing $\text{Intro}_{\ell}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^\nu$ directly, we prove the stronger claim that $Fcom^*(\text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu)) \subseteq Pcoe^\nu$. By the universal property of $Pcoe^\nu$, it suffices to show that $Fcom^*(\text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu))$ is a post-fixed-point of $Pcoe^{-1}$, i.e., that the following holds.

$$Fcom^*(\text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu)) \subseteq Pcoe^{-1}(Fcom^*(\text{Intro}_{\ell}^{\mathcal{K}}?(Pcoe^\nu)))$$