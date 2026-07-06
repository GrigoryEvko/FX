126

General higher inductive types

first rule, we use coherent value introduction. Given any $\Psi'' \Vdash \psi' \in \Psi'$, we are in one of two cases. If $r\psi' = s\psi'$, then $\operatorname{fcoe}_{x,\delta}^{r\to s}(M)\psi' \approx \operatorname{fcoe}_{x,\delta'}^{r\to s}(M')\psi' \in \Downarrow R[\psi, \delta[s/x]]\psi'$ holds by $M\psi' \approx M'\psi' \in \Downarrow R[\psi, \delta[r/x]]\psi'$ combined with the reduction rule we have already proven on both sides. If $r\psi' \neq s\psi'$ then both sides are values, and $\operatorname{fcoe}_{x,\delta}^{r\to s}(M)\psi' \approx \operatorname{fcoe}_{x,\delta'}^{r\to s}(M')\psi' \in Fcoe?(R)[\psi, \delta[r/x]]\psi'$ holds by definition of $Fcoe(R)$. $\square$

We can prove the same kind of lemma for constructing terms in the coherent extension of $Fhcom?(R)$ from terms in the extension of $R$.

**Lemma 6.2.15 (Formal composite introduction).** Let $R$ be a $\Gamma$-PER. Then the following rules are validated for all $\Psi \Vdash \gamma \in \Gamma$, interval terms $\Psi \Vdash r, s \in \mathbb{I}$, and list of constraints $\Psi \Vdash \xi_i \in \mathbb{F}$ for $0 \leq i < n$.

(1)

$$\frac{\begin{array}{c} M \approx M' \in \Downarrow R\gamma \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N'_j \in \Downarrow R\gamma \quad (\forall i) \Psi, \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\gamma \end{array}}{\operatorname{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx \operatorname{fhcom}^{r\to s}(M'; \overline{\xi_i \hookrightarrow x.N'_i}) \in \Downarrow Fhcom?(R)\gamma}$$

(2)

$$\frac{\begin{array}{c} M \in \Downarrow R\gamma \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in \Downarrow R\gamma \quad (\forall i) \Psi, \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\gamma \end{array}}{\operatorname{fhcom}^{r\to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx M \in \Downarrow Fhcom?(R)\gamma}$$

(3)

$$\frac{\begin{array}{c} \Psi \Vdash \xi_k \text{ satisfied} \quad M \in \Downarrow R\gamma \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in \Downarrow R\gamma \quad (\forall i) \Psi, \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\gamma \end{array}}{\operatorname{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx N_k[s/x] \in \Downarrow Fhcom?(R)\gamma}$$

*Proof.* We prove the three rules in reverse order.

(3) By coherent head expansion. For any $\Psi' \Vdash \psi \in \Psi$, there is some minimal $l \leq k$ such that $\xi_l\psi$ is satisfied. Then $\operatorname{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i})\psi \longmapsto N_l[s/x]\psi$, and we have $N_l[s/x] \approx N_k[s/x] \in \Downarrow R\gamma\psi$ by assumption.

(2) Again by coherent head expansion. For any $\Psi' \Vdash \psi \in \Psi$, we are in one of two cases. If there is some minimal $k$ such that $\xi_l\psi$ is satisfied, then $\operatorname{fhcom}^{r\to r}(M; \overline{\xi_i \hookrightarrow x.N_i})\psi \longmapsto N_k[s/x]\psi$ and we have $N_k[s/x] \approx M \in \Downarrow R\gamma\psi$ by assumption. Otherwise, we have $\operatorname{fhcom}^{r\to r}(M; \overline{\xi_i \hookrightarrow x.N_i})\psi \longmapsto M\psi$, and $M\psi$ is in $\Downarrow R\gamma\psi$ by assumption.