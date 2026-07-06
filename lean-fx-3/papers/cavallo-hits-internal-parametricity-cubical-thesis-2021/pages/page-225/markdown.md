Bicubical set model

213

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_0 \text{ type} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_1 \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.A_0.A_1[\mathrm{p}] \vdash R \text{ type}}{\Gamma \vdash \operatorname{Gel}_r(A_0, A_1, R) \text{ type}}$$

$$\frac{\varepsilon \in \{0, 1\} \quad \Gamma \vdash A_0 \text{ type} \quad \Gamma \vdash A_1 \text{ type} \quad \Gamma.A_0.A_1[\mathrm{p}] \vdash R \text{ type}}{\Gamma \vdash \operatorname{Gel}_\varepsilon(A_0[\varepsilon_1^\dagger], A_1[\varepsilon_1^\dagger], R[\varepsilon_1^{\dagger \times \times}]) = A_\varepsilon \text{ type}}$$

$$\frac{\Gamma.\backslash\boldsymbol{r} \vdash M_1 : A_1 \quad \Gamma.\backslash\boldsymbol{r}.A_0.A_1[\mathrm{p}] \vdash R \text{ type} \quad \Gamma.\backslash\boldsymbol{r} \vdash P : R[\operatorname{id}.M_0.M_1]}{\Gamma \vdash \operatorname{gel}_r(M_0, M_1, P) : \operatorname{Gel}_r(A_0, A_1, R)}$$

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathrm{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\operatorname{id}.M_0.M_1]}{\Gamma \vdash \operatorname{gel}_\varepsilon(M_0[\varepsilon_1^\dagger], M_1[\varepsilon_1^\dagger], P[\varepsilon_1^\dagger]) = M_\varepsilon : A_\varepsilon}$$

$$\frac{\Gamma \vdash A_0 \text{ type} \quad \Gamma \vdash A_1 \text{ type} \quad \Gamma.A_0.A_1[\mathrm{p}] \vdash R \text{ type} \quad \Gamma.\mathbf{I} \vdash Q : \operatorname{Gel}_{\mathrm{v}_1}(A_0[\operatorname{id}^\dagger], A_1[\operatorname{id}^\dagger], R[\operatorname{id}^{\dagger \times \times}])}{\Gamma \vdash \operatorname{ungel}(Q) : R[\operatorname{id}.Q[\mathbf{0}_1].Q[\mathbf{1}_1]]}$$

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathrm{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\operatorname{id}.M_0.M_1]}{\Gamma \vdash \operatorname{ungel}(\operatorname{gel}_{\mathrm{v}_1}(M_0[\operatorname{id}^\dagger], M_1[\operatorname{id}^\dagger], P[\operatorname{id}^\dagger])) = P : R[\operatorname{id}.M_0.M_1]}$$

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_0 \text{ type} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_1 \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.A_0.A_1[\mathrm{p}] \vdash R \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash Q : \operatorname{Gel}_{\mathrm{v}_1}(A_0[\operatorname{id}^\dagger], A_1[\operatorname{id}^\dagger], R[\operatorname{id}^{\dagger \times \times}])}{\Gamma \vdash Q[\operatorname{id}.\boldsymbol{r}] = \operatorname{gel}_r(Q[\mathbf{0}_1], Q[\mathbf{1}_1], \operatorname{ungel}(Q)) : \operatorname{Gel}_r(A_0, A_1, R)}$$

Figure 11.2: Rules for Gel types in a parametric type theory formalism