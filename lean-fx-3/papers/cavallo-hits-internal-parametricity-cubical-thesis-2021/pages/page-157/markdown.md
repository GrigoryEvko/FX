Elimination 145

- $r\psi' = s\psi'$. Then $\text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; F_s; \mathcal{E}\psi)\psi' \longmapsto E\psi'$. We know that $\Psi' \Vdash F_r\psi' = M\psi' \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta)\psi'$ by fcoe introduction for the inductive type (Lemma 6.2.14). By the principles required of coercion in $D$, it follows that $\Psi'' \Vdash E\psi' = \text{coe}_{x.D\psi[\delta',M/h]}^{r\rightarrow s}(E)\psi' \in D[\delta, F_r/h]\psi'$.
- $r\psi' \neq s\psi'$. Then $\text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; F_s; \mathcal{E}\psi)\psi' \longmapsto \text{coe}_{x.D\psi[\delta',F_s/h]}^{r\rightarrow s}(E)\psi'$, and we know that the reduct is well-typed by coercion in $D$. $\square$

**Corollary 6.4.8.** $Fcoe(Elim^{-1}) \subseteq Elim^{-1}$.

*Proof.* As in the proof of Corollary 6.3.10 for coercion: given two applications of fcoe to equal eliminable terms, we can show that the results are equal by applying Lemma 6.4.7. $\square$

**Lemma 6.4.9 (Reduction of elim on fhcom).** The following rule is validated for any substitutions $\Psi' \Vdash (\psi, \delta) \in (\Psi, \Delta)$.

$$\begin{array}{c} \Psi' \Vdash r, s \in \mathbb{I} \quad (\forall i) \Psi' \Vdash \xi_i \in \mathbb{F} \\ M \in \Downarrow Elim^{-1}[\psi, \delta] \quad (\forall i, j) \Psi', \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in \Downarrow Elim^{-1}[\psi, \delta] \\ (\forall i) \Psi', \xi_i \gg M \approx N_i[s/x] \in \Downarrow Elim^{-1}[\psi, \delta] \quad F_x := \text{fhcom}^{r\rightarrow x}(M; \overline{\xi_i \hookrightarrow x.N_i}) \\ E := \text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; M; \mathcal{E}\psi) \quad (\forall i) E_i := \text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; N_i; \mathcal{E}\psi) \\ \hline \Psi' \Vdash \text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; F_s; \mathcal{E}\psi) = \text{com}_{x.D\psi[\delta,F_s/h]}^{r\rightarrow s}(E; \overline{\xi_i \hookrightarrow x.E_i}) \in D[\delta, F_s/h] \end{array}$$

*Proof.* Straightforward application of coherent head expansion following the pattern of Lemma 6.4.7. $\square$

**Corollary 6.4.10.** $Fhcom(Elim^{-1}) \subseteq Elim^{-1}$.

The case of constructor terms is, as usual, entangled with a property of interpretations, here the well-typedness of the $\overline{\text{act}}$ operator.

**Lemma 6.4.11 (Action of argument contexts and types).** Let $n \in \mathbb{N}$ and let $R \subseteq \text{Ind}_{\mathcal{K}}$ be a $(\Psi, \Delta)$-relation such that $Fcoe(R) \subseteq R$, $Fhcom(R) \subseteq R$, and $Intro_{\ell}^{\mathcal{K}}(R) \subseteq R$ for all $\ell$ with $|\ell|_{\mathcal{K}} < n$. Finally, let $\bar{v}_{\Delta}.h.T, \bar{v}_{\Delta}.h.T'$ be terms such that $\Psi' \Vdash T[\gamma, M/h] = T'[\gamma', M'/h] \in D[\gamma, M/h]$ for all $\Psi' \Vdash \gamma = \gamma' \in (\Psi, \Delta)$ and $M \approx M' \in \Downarrow R\gamma$. Then the following rule is validated for all $\Psi' \Vdash \psi \in \Psi$.

$$\frac{\Psi' \Vdash \Delta\psi \mid \mathcal{K}\psi \blacktriangleright \Theta = \Theta' \text{ actx} \quad |\Theta|_{\mathcal{K}\psi} < n \quad \chi \approx \chi' \in \{\Theta\}_{\mathcal{K}\psi}(R\psi)}{\Psi' \Vdash \overline{\text{act}}(\Theta; \bar{v}_{\Delta}.h.T\psi; \chi) = \overline{\text{act}}(\Theta'; \bar{v}_{\Delta}.h.T'\psi; \chi') \in \{\Theta\}_{\mathcal{K}\psi, \mathcal{E}\psi}^{\Delta\psi.h.D\psi}(\chi)}$$