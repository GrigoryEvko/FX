Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:57

TM-GEL-BOUNDARY

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\text{id.}M_0.M_1]}{\Gamma \vdash \text{gel}_\varepsilon(M_0[\varepsilon_\mathbf{I}^\dagger], M_1[\varepsilon_\mathbf{I}^\dagger], P[\varepsilon_\mathbf{I}^\dagger]) = M_\varepsilon : A_\varepsilon}$$

TM-UNGEL

$$\frac{\Gamma \vdash A_0 \text{ type}}{\Gamma \vdash A_1 \text{ type} \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma.\mathbf{I} \vdash Q : \text{Gel}_{\mathfrak{q}_\mathbf{I}}(A_0[\text{id}^\dagger], A_1[\text{id}^\dagger], R[\text{id}^{\dagger \times \times}])} \quad \Gamma \vdash \text{ungel}(Q) : R[\text{id.}Q[\mathbf{0}_\mathbf{I}].Q[\mathbf{1}_\mathbf{I}]]$$

TM-GEL-BETA

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\text{id.}M_0.M_1]}{\Gamma \vdash \text{ungel}(\text{gel}_{\mathfrak{q}_\mathbf{I}}(M_0[\text{id}^\dagger], M_1[\text{id}^\dagger], P[\text{id}^\dagger])) = P : R[\text{id.}M_0.M_1]}$$

TM-GEL-ETA

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_0 \text{ type} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_1 \text{ type}}{\Gamma.\backslash\boldsymbol{r}.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash Q : \text{Gel}_{\mathfrak{q}_\mathbf{I}}(A_0[\text{id}^\dagger], A_1[\text{id}^\dagger], R[\text{id}^{\dagger \times \times}])} \quad \Gamma \vdash Q[\text{id.}\boldsymbol{r}] = \text{gel}_\boldsymbol{r}(Q[\mathbf{0}_\mathbf{I}], Q[\mathbf{1}_\mathbf{I}], \text{ungel}(Q)) : \text{Gel}_\boldsymbol{r}(A_0, A_1, R)$$

### A.12. Extent.

TM-EXTENT

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash A \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I}.A \vdash B \text{ type}}{\Gamma \vdash M : A[\text{id.}\boldsymbol{r}] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_\boldsymbol{r}(M; N_0, N_1, N) : B[\text{id.}\boldsymbol{r}.M]}$$

TM-EXTENT-BOUNDARY

$$\frac{\varepsilon \in \{0, 1\} \quad \Gamma.\mathbf{I} \vdash A \text{ type}}{\Gamma.\mathbf{I}.A \vdash B \text{ type} \quad \Gamma \vdash M : A[\varepsilon_\mathbf{I}] \quad \Gamma.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_{\mathfrak{q}_\mathbf{I}[\varepsilon_\mathbf{I}]}(M; N_0[\varepsilon_\mathbf{I}^{\dagger \times}], N_1[\text{id}^{\dagger \times}], N[\text{id}^{\dagger \times \times \times}]) = N_\varepsilon[\text{id.}M] : B[\varepsilon_\mathbf{I}.M]}$$

TM-EXTENT-BETA

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash A \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I}.A \vdash B \text{ type}}{\Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash M : A \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_\boldsymbol{r}(M[\text{id.}\boldsymbol{r}]; N_0, N_1, N) = N[\text{id.}M[\mathbf{0}_\mathbf{I}].M[\mathbf{1}_\mathbf{I}].\lambda^\mathbf{I}.M]@\boldsymbol{r} : B[\text{id.}\boldsymbol{r}.M]}$$

## REFERENCES

[ABC+19] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. Syntax and models of cartesian cubical type theory. Unpublished draft, February 2019.

[ACS15] Benedikt Ahrens, Paolo Capriotti, and Régis Spadotti. Non-wellfounded trees in homotopy type theory. In Thorsten Altenkirch, editor, 13th International Conference on Typed Lambda Calculi and Applications, TLCA 2015, July 1-3, 2015, Warsaw, Poland, volume 38 of LIPIcs, pages 17-30. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2015.