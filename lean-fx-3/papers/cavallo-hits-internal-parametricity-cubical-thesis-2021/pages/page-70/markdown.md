58

Cubical type theory

$\Gamma$-relation $R$ and terms $M, M'$, we write $\Gamma \gg M \approx M' \in R$ to mean that $M\gamma \approx M'\gamma' \in R\langle\gamma\rangle$ holds for all $\Psi \Vdash \gamma \in \Gamma$.

Note that while the definitions of $\Psi$- and $R$-relations are dependent only on the theory of interval substitutions, the definition of $\Gamma$-relation is of course relative to a type system.

### 3.1.4 Kan operations and types

Finally, we define the conditions under which a pretype becomes a type: when it supports the coercion and homogeneous composition operations.

**Definition 3.1.26 (Coercion).** We say that a $\Psi$-relation $R$ *supports coercion at $A, A'$* when it validates the following rules for every $\Psi', x : \mathbb{I} \Vdash \psi \in \Psi$ and $\Psi' \Vdash r, s \in \mathbb{I}$.

$$\frac{M \approx M' \in \Downarrow R[\psi, r/x]}{\text{coe}_{x.A\psi}^{r \to s}(M) \approx \text{coe}_{x.A'\psi}^{r \to s}(M') \in \Downarrow R[\psi, s/x]} \quad \frac{M \in \Downarrow R[\psi, r/x]}{\text{coe}_{x.A\psi}^{r \to r}(M) \approx M \in \Downarrow R[\psi, r/x]}$$

That is, a relation $R$ supports coercion at $A, A'$ when we can coerce along any substitution instance $R\psi$ that forms a line of types in some direction $x$; moreover, we require that the trivial coercion $r \to r$ is equal to the identity function. We say that $\Psi \Vdash A = A'$ pretype support coercion when $[[A]]$ (equivalently, $[[A']]$) supports coercion at $A, A'$.

**Definition 3.1.27 (Homogeneous composition).** We say that a $\Psi$-relation $R$ *supports homogeneous composition at $A, A'$* when it validates the following rules for every $\Psi' \Vdash \psi \in \Psi$, interval terms $\Psi' \Vdash r, s \in \mathbb{I}$, and list of constraints $\Psi' \Vdash \xi_i \in \mathbb{F}$ for $0 \le i < n$.

$$\frac{M \approx M' \in R\psi}{(\forall i, j) \ \Psi', \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N'_j \in \Downarrow R\psi \quad (\forall i) \ \Psi', \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\psi} \quad \frac{\text{hcom}_{A\psi}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx \text{hcom}_{A'\psi}^{r \to s}(M'; \overline{\xi_i \hookrightarrow x.N'_i}) \in \Downarrow R\psi}{}$$

$$\frac{M \in \Downarrow R\psi}{(\forall i, j) \ \Psi', \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in \Downarrow R\psi \quad (\forall i) \ \Psi', \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\psi} \quad \frac{\text{hcom}_{A\psi}^{r \to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx M \in \Downarrow R\psi}{}$$

$$\frac{\Psi' \Vdash \xi_k \text{ satisfied} \quad M \in \Downarrow R\psi}{(\forall i, j) \ \Psi', \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in \Downarrow R\psi \quad (\forall i) \ \Psi', \xi_i \gg M \approx N_i[r/x] \in \Downarrow R\psi} \quad \frac{\text{hcom}_{A\psi}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \approx N_k[s/x] \in \Downarrow R\psi}{}$$