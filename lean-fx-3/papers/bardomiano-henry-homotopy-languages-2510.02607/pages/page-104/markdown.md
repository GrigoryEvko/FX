**Lemma A.26.** *If $I$ is an interpretation of $T$ into $T'$ and we have expressions $f$ and $\{t_\alpha\}_{\alpha<\lambda}$ on the alphabet $A_T$, then*

$$\widetilde{I}(f[t_\alpha \mid x_\alpha]_{\alpha<\lambda}) = \widetilde{I}(f)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda}.$$

*Proof.* This is done by induction on the length of $f$ in [Car78, Lemma 1, pp. 1.52]. The interesting case is when $f = F(e_\beta)_{\beta<\mu}$ for some $F$ in the alphabet and expressions $\{e_\beta\}_{\beta<\mu}$. We assume inductively the result true for the expressions $\{e_\beta\}_{\beta<\mu}$. Then we have:

$$\begin{aligned} \widetilde{I}(f[t_\alpha \mid x_\alpha]_{\alpha<\lambda}) &= \widetilde{I}(F(e_\beta[t_\alpha \mid x_\alpha]_{\alpha<\lambda})_{\beta<\mu}) \\ &= I(F)(\widetilde{I}(e_\beta[t_\alpha \mid x_\alpha]_{\alpha<\lambda}))_{\beta<\mu} \\ &= I(F)(\widetilde{I}(e_\beta)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda})_{\beta<\mu}, \text{ by induction hypothesis} \\ &= I(F)(\widetilde{I}(e_\beta))_{\beta<\mu}[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \\ &= \widetilde{I}(F(e_\beta)_{\beta<\mu})[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \\ &= \widetilde{I}(f)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \end{aligned}$$

□

There is also a notion of composition of interpretations: If $I : S \rightarrow T$ and $J : T \rightarrow U$ are interpretations, then there is an interpretation $J \circ I : S \rightarrow U$ that is defined in the obvious way. It is also easy to infer what is the identity for this composition. A crucial result to define these compositions is:

**Lemma A.27.** *If $I : S \rightarrow T$ and $J : T \rightarrow U$ are interpretations then $\widetilde{J \circ I}(e) = \widetilde{J}(\widetilde{I}(e))$*

*Proof.* This is by induction of the expression $e$ see [Car78, Lemma 3, pp. 1.55]. □

We can define the category $\kappa$-GAT of $\kappa$-generalized algebraic theories. There is an equivalence relation on interpretations between two theories $T$ and $T'$. If $I, J : T \rightarrow T'$ are two interpretations, then $I \approx J$ if an only if for every rule $r \in R_U$ we have $I(r) \approx J(r)$ in the theory $T'$.

**Lemma A.28.** *If $I$ and $J$ are interpretations from $T$ to $T'$ such that $I \approx J$ then for all type and element judgments $\mathcal{J}$ of $U$, $\widetilde{I}(\mathcal{J}) \approx \widetilde{J}(\mathcal{J})$ in $T'$.*

*Proof.* See [Car78, Lemma 1, Section 1.14]. □

□

104