256

Cohesive parametric type theory

# Coercion

$$\frac{\mu \in \{\text{dsc, glo}\}}{\text{coe}_{x.\langle\mu|A\rangle}^{r\to s}(P) \longmapsto \text{mod}(\text{coe}_{x.A}^{r\to s}(\text{unmod}(P')))}$$

$$\frac{P \longmapsto P'}{\text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(P) \longmapsto \text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(P')} \quad \frac{\text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(\text{mod}(M)) \longmapsto \text{mod}(\text{coe}_{x.A}^{r\to s}(M))}{\text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(\text{fhcom}^{t\to u}(P; \overline{\xi_i \hookrightarrow y.P_i})) \longmapsto \text{fhcom}^{t\to u}(\text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(P); \overline{\xi_i \hookrightarrow y.\text{coe}_{x.\langle\text{cc}|A\rangle}^{r\to s}(P_i))}}$$

# Composition

$$\frac{\mu \in \{\text{dsc, glo}\}}{\text{hcom}_{\langle\mu|A\rangle}^{r\to s}(P; \overline{\xi_i \hookrightarrow x.P_i}) \longmapsto \text{mod}(\text{hcom}_A^{r\to s}(\text{unmod}(P); \overline{\xi_i \hookrightarrow x.\text{unmod}(P_i)}))} \quad \frac{\text{hcom}_{\langle\text{cc}|A\rangle}^{r\to s}(P; \overline{\xi_i \hookrightarrow x.P_i}) \longmapsto \text{fhcom}^{r\to s}(P; \overline{\xi_i \hookrightarrow x.P_i})}{}$$

# Formal composites

$$\frac{r \neq s \quad (\nexists i) \xi_i \text{ satisfied}}{\text{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \text{ val}} \quad \frac{(\nexists i) \xi_i \text{ satisfied}}{\text{fhcom}^{r\to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto M}$$

$$\frac{(\nexists i < k) \xi_i \text{ satisfied} \quad \xi_k \text{ satisfied}}{\text{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto N_k[s/x]}$$

Figure 14.5: Operational semantics for modal parametric type theory: Kan operations