174

Parametric cubical type theory

# **Bridges**

$$\overline{\text{Bridge}(\boldsymbol{x}.A, M, N) \text{ val}} \quad \overline{\lambda^{\mathbf{I}}\boldsymbol{x}.M \text{ val}} \quad \frac{P \longmapsto P'}{P\boldsymbol{r} \longmapsto P'\boldsymbol{r}} \quad \overline{(\lambda^{\mathbf{I}}\boldsymbol{x}.M)\boldsymbol{r} \longmapsto P[\boldsymbol{r}/\boldsymbol{x}]}$$

$$\overline{\text{coe}_{x.\text{Bridge}(\boldsymbol{y}.A,M_0,M_1)}^{r\to s}(P) \longmapsto \lambda^{\mathbf{I}}\boldsymbol{y}.\text{com}_{x.A}^{r\to s}(P; \boldsymbol{y} \equiv \mathbf{0} \hookrightarrow x.M_0, \boldsymbol{y} \equiv \mathbf{1} \hookrightarrow x.M_1)}$$

$$\underline{\text{hcom}_{\text{Bridge}(\boldsymbol{y}.A,M_0,M_1)}^{r\to s}(P; \overline{\xi_i \hookrightarrow x.Q_i})}$$

$$\lambda^{\mathbf{I}}\boldsymbol{y}.\text{hcom}_A^{r\to s}(P\boldsymbol{y}; \overline{\xi_i \hookrightarrow x.Q_i}\boldsymbol{y}, \boldsymbol{y} \equiv \mathbf{0} \hookrightarrow ...M_0, \boldsymbol{y} \equiv \mathbf{1} \hookrightarrow ...M_1)$$

# **Gel types**

$$\overline{\text{Gel}_x(A_0, A_1, a.b.R) \text{ val}} \quad \overline{\text{Gel}_\varepsilon(A_0, A_1, a.b.R) \longmapsto A_\varepsilon}$$

$$\overline{\text{gel}_x(M_0, M_1, P) \text{ val}} \quad \overline{\text{gel}_\varepsilon(M_0, M_1, P) \longmapsto M_\varepsilon}$$

$$\frac{Q \longmapsto Q'}{\text{ungel}(\boldsymbol{x}.Q) \longmapsto \text{ungel}(\boldsymbol{x}.Q')} \quad \frac{\boldsymbol{x} \notin P}{\text{ungel}(\boldsymbol{x}.\text{gel}_x(M_0, M_1, P)) \longmapsto P}$$

$$M_\varepsilon^y := \text{hcom}_{A_\varepsilon}^{r\to y}(Q[\varepsilon/\boldsymbol{x}]; \overline{\xi_i[\varepsilon/\boldsymbol{x}] \hookrightarrow y.Q_i[\varepsilon/\boldsymbol{x}]}$$

$$P := \text{com}_{y.R[M_0^y/a_0,M_1^y/a_1]}^{r\to s}(\text{ungel}(\boldsymbol{x}.Q); (\overline{\xi_i \hookrightarrow y.\text{ungel}(\boldsymbol{x}.Q_i)})_{\boldsymbol{x} \notin \xi_i})$$

$$\underline{\text{hcom}_{\text{Gel}_x(A_0,A_1,a_0,a_1.R)}^{r\to s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) \longmapsto \text{gel}_x(M_0^s, M_1^s, P)}$$

$$M_\varepsilon^y := \text{coe}_{y.A_\varepsilon}^{r\to y}(Q[\varepsilon/\boldsymbol{x}]) \quad P := \text{coe}_{y.R[M_0^y/a_0,M_1^y/a_1]}^{r\to s}(\text{ungel}(\boldsymbol{x}.Q))$$

$$\underline{\text{coe}_{y.\text{Gel}_x(A_0,A_1,a_0,a_1.R)}^{r\to s}(Q) \longmapsto \text{gel}_x(M_0^s, M_1^s, P)}$$

# **The extent operator**

$$\overline{\text{extent}_\varepsilon(M; a_0.N_0, a_1.N_1, a_0.a_1.\overline{a}.\overline{N}) \longmapsto N_\varepsilon[M/a]}$$

$$\underline{\text{extent}_x(M; a_0.N_0, a_1.N_1, a_0.a_1.\overline{a}.\overline{N}) \longmapsto \overline{N}[M[\mathbf{0}/\boldsymbol{x}]/a_0, M[\mathbf{1}/\boldsymbol{x}]/a_1, \lambda^{\mathbf{I}}\boldsymbol{x}.M/\overline{a}]\boldsymbol{x}}$$

Figure 9.1: Additional operational semantics for parametric type theory