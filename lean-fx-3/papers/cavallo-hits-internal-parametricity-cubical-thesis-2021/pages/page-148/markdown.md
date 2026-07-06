136

General higher inductive types

Proof. Given any $V \approx V' \in Fcoe(Pcoe^{-1}(R))\langle\psi, \delta\rangle$, we have that $V$ and $V'$ are fcoe terms with well-typed boundaries. When we apply pcoe to the two, each reduces to a term to which it is related in $Fcoe?(R)$ by Lemma 6.3.9. These two reducts are in turn related to each other in $Fcoe?(R)$, and related to $V$ and $V'$ in $Fcoe?(R)$ when the pcoe is trivial, by Lemmas 6.3.8 and 6.2.14. Thus we have $V \approx V' \in Pcoe^{-1}(Fcoe?(R))\langle\psi, \delta\rangle$. $\square$

Corollary 6.3.11. We have $Fcoe?(Pcoe^v) \subseteq Pcoe^v$.

Proof. It suffices to show that $Fcoe?$ is a post-fixed-point of $Pcoe^{-1}$. Using Corollary 6.3.10, we have $Fcoe?(Pcoe^v) = Fcoe?(Pcoe^{-1}(Pcoe^v)) \subseteq Pcoe^{-1}(Fcoe?(Pcoe^v))$. $\square$

Lemma 6.3.12 (Reduction of pcoe on fhcom). The following rule is validated for any $(\Psi, \Delta)$-PER $R$, substitution $\Psi', x : \mathbb{I} \Vdash \psi \in \Psi$, $\Psi' \Vdash r, s \in \mathbb{I}$, and $\Psi' \Vdash \delta \in \Delta\psi[r/x]$.

$$\begin{array}{l} \Psi' \Vdash t, u \in \mathbb{I} \quad (\forall i) \Psi' \Vdash \xi_i \in \mathbb{F} \quad M \in \Downarrow Pcoe^{-1}(R)[\psi[r/x], \delta] \\ (\forall i, j) \Psi', \xi_i, \xi_j, y : \mathbb{I} \gg N_i \approx N_j \in \Downarrow Pcoe^{-1}(R)[\psi[r/x], \delta] \\ (\forall i) \Psi', \xi_i \gg M \approx N_i[t/y] \in \Downarrow Pcoe^{-1}(R)[\psi[r/x], \delta] \\ \hline \mathrm{pcoe}_{x.\mathcal{K}\psi \blacktriangleright x.\Delta\psi}^{r \to s}(\mathrm{fhcom}^{t \to u}(M; \overline{\xi_i \hookrightarrow y.N_i})) \\ \approx \\ \mathrm{fhcom}^{t \to u}(\mathrm{pcoe}_{x.\Delta\psi \blacktriangleright x.\mathcal{K}\psi}^{r \to s}(M); \overline{\xi_i \hookrightarrow y.\mathrm{pcoe}_{x.\Delta\blacktriangleright x.\mathcal{K}}^{r \to s}(N_i)}) \\ \in \\ \Downarrow Fhcom?(R)[\psi[s/x], \overline{\mathrm{coe}}_{x.\Delta\psi}^{r \to s}(\delta)] \end{array}$$

Proof. Again by a straightforward application of coherent head expansion, now using Lemma 6.2.15 to check that the right side is in the desired relation. $\square$

Corollary 6.3.13. For any $R$, we have $Fhcom(Pcoe^{-1}(R)) \subseteq Pcoe^{-1}(Fhcom?(R))$.

Proof. As with Corollary 6.3.10. $\square$

Corollary 6.3.14. We have $Fhcom?(Pcoe^v) \subseteq Pcoe^v$.

Proof. As with Corollary 6.3.11. $\square$

Definition 6.3.15. Define $Fcom(R) := Fhcom(Fcoe?(R))$.

Lemma 6.3.16. For any $R$, we have $Fcom(Pcoe^{-1}(R)) \subseteq Pcoe^{-1}(Fcom?(R))$.

Proof. By Corollaries 6.3.10 and 6.3.13. $\square$