120

General higher inductive types

# Type former

$$\overline{\operatorname{Ind}_{\mathcal{K}}^{\Delta}(\delta) \text{ val}}$$

# Constructors

$$\frac{(\ell : \Psi.\Omega.[\delta; \Theta.\overline{\xi_i \hookrightarrow \mathrm{M}_i}]) \in \mathcal{K} \quad (\nexists i) \ \xi_i \text{ satisfied}}{\operatorname{intro}_{\ell}^{\mathcal{K}}(\phi; \omega; \chi) \text{ val}}$$

$$\frac{(\ell : \Psi.\Omega.[\delta; \Theta.\overline{\xi_i \hookrightarrow \mathrm{M}_i}]) \in \mathcal{K} \quad (\nexists i < k) \ \xi_i \text{ satisfied} \quad \xi_k \text{ satisfied}}{\operatorname{intro}_{\ell}^{\mathcal{K}}(\phi; \omega; \chi) \longmapsto (\Theta.\mathrm{M}_k[\phi, \omega])_{\mathcal{K}}(\chi)}$$

# Formal coercions

$$\frac{r \neq s}{\operatorname{fcoe}_{x.\delta}^{r \to s}(M) \text{ val}}$$

$$\overline{\operatorname{fcoe}_{x.\delta}^{r \to r}(M) \longmapsto M}$$

# Formal composites

$$\frac{r \neq s \quad (\nexists i) \ \xi_i \text{ satisfied}}{\operatorname{fhcom}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \text{ val}}$$

$$\frac{(\nexists i) \ \xi_i \text{ satisfied}}{\operatorname{fhcom}^{r \to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto M}$$

$$\frac{(\nexists i < k) \ \xi_i \text{ satisfied} \quad \xi_k \text{ satisfied}}{\operatorname{fhcom}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto N_k[s/x]}$$

# Formal heterogeneous composites

$$\operatorname{fcom}_{x.\delta}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) := \operatorname{fhcom}^{r \to s}(\operatorname{fcoe}_{x.\delta}^{r \to s}(M); \overline{\xi_i \hookrightarrow x.\operatorname{fcoe}_{x.\delta}^{x \to s}(x.N_i)})$$

Figure 6.5: Operational semantics for formation and introduction in HITs