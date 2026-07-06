**4.2 Notation.** Because $\iota_p$ is the inclusion of a full subcategory, we will often identify $X$ and $\iota_p X$ in our notation. In the same way, for a morphism $f \in \operatorname{Hom}(X, \tau_m(Y))$, the corresponding morphism in $\operatorname{Hom}(\iota_p X, Y)$ will also be denoted $f$.

**4.3 Proposition.** *For $m < p$, the adjoint pairs $(\pi_m \dashv \iota_p)$ and $(\iota_p \dashv \tau_m)$ are Quillen pairs (definition Definition A.5) both between $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ and $\infty\text{-Cat}_{\text{Sat-Ind}}^{+p}$ and between $\infty\text{-Cat}_{\text{Ind}}^{+m}$ and $\infty\text{-Cat}_{\text{Ind}}^{+p}$.*

*Proof.* The left adjoint functors $\pi_m$ and $\iota_p$ obviously preserve cofibrations. Their respective right adjoint functors $\iota_p$ and $\tau_m$ obviously preserve the isofibrations of Section 3.3, and fibrant objects for either the inductive (characterized by Definition 3.18 and Proposition 3.25) or saturated inductive model structures (whose characterization is given in Lemma 3.37). This implies that the right adjoint functors preserve fibrations between fibrant objects. The left adjoint then also preserves acyclic cofibrations as well, and this concludes the proof. $\square$

**4.4 Proposition.** *For any $m < p \leq \infty$, a morphism $f$ in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ is a cofibration (resp. acyclic cofibration, resp. fibration, resp. acyclic fibration, resp. weak equivalence) if and only if $\iota_p(f)$ is in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+p}$.*

*Proof.* This directly follows from Proposition 4.3 and from the fact that $\iota_p$ is the inclusion of a full subcategory. $\square$

As mentioned in the introduction, we can consider the two towers of left semi-model structures:

$$\begin{aligned} &\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \xleftarrow{\tau_n} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \xleftarrow{\tau_1} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \xleftarrow{\tau_2} \dots \xleftarrow{\tau_{n-1}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \xleftarrow{\tau_n} \dots \\ &\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \xleftarrow{\tau_n} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \xleftarrow{\tau_1} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \xleftarrow{\tau_2} \dots \xleftarrow{\tau_{n-1}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \xleftarrow{\tau_n} \dots \end{aligned}$$

and take the projective limit of either tower to get a definition of 'strict $(\infty, \infty)$-categories'.

Our goal in this section is to show that the left semi-model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$ is equivalent to the limit of the second tower (with $\tau$ functors). Here, by projective limit, we mean a homotopy theoretic limit of these towers, that is, a homotopy limit of the corresponding tower of $(\infty, 1)$-categories. Such projective limits of model structures have been studied in [11] and [20], and we will use the construction from these papers.

**4.5 Remark.** It should be noted that the results from [11] and [20] are only proved for Quillen model structures, so they do not immediately apply to the left semi-model structures that we are using here. The proof from these two papers easily adapts to the setting of left semi-model structures with very few modifications, so it should be safe to assume these results can be applied here as well. Though to avoid relying on this, we will give an independent proof that the left semi-model structure we use as a model of these projective limits exists and state our main theorem as an equivalence with this left semi-model structure. The only aspect that still relies on applying the results of [11] or [20] to left semi-model structures is in order to interpret our results as saying something about homotopy limits of towers.

37