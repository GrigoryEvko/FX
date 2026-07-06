**Lemma B.36.** Let $\{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu} \vdash \Omega$ a rule such that $H$ is satisfied. If $\langle t_{\beta} \rangle_{\beta < \mu} : \{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \to \{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu}$ is a map such that $H(r_{t_{\beta}})$ for all $\beta < \mu$ then $H(\{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu} \vdash \Omega[t_{\beta}|x_{\beta}]_{\beta < \mu})$

*Proof.* By induction on $\mu$ and treating all the different cases for $H$. The proof in [Car78, Lemma 11 pp.2.56] works here too. $\square$

**Lemma B.37.** 1. For any object $A_{\lambda} \in \mathcal{C}$, we have:

(a) $A\lambda = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\lambda}}(x_{\alpha})_{\alpha < \lambda} \text{ Type})$.
(b) For all $\alpha < \lambda$, $\delta_{p_{\alpha}^{\lambda}} = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha})$ where $p_{\alpha}^{\lambda} : A_{\lambda} \twoheadrightarrow A_{\alpha}$.

2. For any non-trivial object $A_{\lambda}$ and $f : A_{\lambda} \to B_{\mu+1}$, $\delta_f = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_{\alpha})_{\alpha < \lambda} \overline{(p_{\mu}f)^*B}(x_{\alpha})_{\alpha < \lambda})$ where $p_{\mu} : B_{\mu+1} \twoheadrightarrow B_{\mu}$.

*Proof.* This is [Car78, Lemma 12 pp.263]. $\square$

**Lemma B.38.** Every derived rule of $U(\mathcal{C})$ satisfies the hypothesis $H$.

*Proof.* This is by induction on derived rules of $U(\mathcal{C})$. Indeed, [Car78, Lemma pp.2.65] shows that every derivation from theorem A.4 preserves $H$. $\square$

**Corollary B.39.** 1. For any type symbol $\overline{A_{\lambda}}$ of the theory $U(\mathcal{C})$ we have $H(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\lambda}}(x_{\alpha})_{\alpha < \lambda} \text{ Type})$.

2. For every operator symbol $\overline{f}$ in $U(\mathcal{C})$ where $f : A_{\lambda} \to B_{\mu+1}$ we have $H(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_{\alpha})_{\alpha < \lambda} \overline{(p_{\mu}f)^*B}(x_{\alpha})_{\alpha < \lambda})$.

The foremost important result, which summarizes the above, is:

**Corollary B.40.** 1. If $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda}$ is a context of the theory then for any $\alpha < \delta < \lambda$ we have $ht(r_{\Delta_{\alpha}}) < ht(r_{\Delta_{\beta}})$.

2. If there is a map $\langle t_{\beta} \rangle_{\beta < \mu} : \{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \to \{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu}$ then for each $\beta < \mu$ we have $\mathcal{J}(r_{t_{\beta}}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta}}))$ where $r_{\Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta}}$ is the rule $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \vdash \Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta} \text{ Type}$.
3. If $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \equiv \{x_{\alpha} : \Delta'_{\alpha}\}_{\alpha < \lambda}$ then $\mathcal{J}(r_{\Delta_{\lambda}}) = \mathcal{J}(r_{\Delta'_{\lambda}})$.
4. If $\langle t_{\alpha} \rangle_{\alpha < \lambda} \equiv \langle t'_{\alpha} \rangle_{\alpha < \lambda}$ then for each $\beta < \mu$, $\mathcal{J}(r_{t_{\beta}}) = \mathcal{J}(r_{t'_{\beta}})$.

We are almost ready to define a contextual functor $\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$. We only need the next:

131