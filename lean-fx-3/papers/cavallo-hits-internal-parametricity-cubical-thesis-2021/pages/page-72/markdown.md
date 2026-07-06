60

Cubical type theory

# Paths

$$\overline{\text{Path}(x.A, M, N) \text{ val}} \quad \overline{\lambda^{\mathbb{I}}x. M \text{ val}} \quad \frac{P \longmapsto P'}{P r \longmapsto P' r} \quad \overline{(\lambda^{\mathbb{I}}x. M) r \longmapsto P[r/x]}$$

# V types

$$\begin{array}{l} \overline{\mathrm{V}_x(A_0, A_1, I) \text{ val}} \quad \overline{\mathrm{V}_\varepsilon(A_0, A_1, I) \longmapsto A_\varepsilon} \quad \overline{\mathrm{v}_x(M_0, M_1) \text{ val}} \quad \overline{\mathrm{v}_\varepsilon(M_0, M_1) \longmapsto M_\varepsilon} \\ \frac{M \longmapsto M'}{\mathrm{vproj}_x(M, I) \longmapsto \mathrm{vproj}_x(M', I)} \quad \overline{\mathrm{vproj}_x(\mathrm{v}_x(M, N), I) \longmapsto N} \\ \overline{\mathrm{vproj}_0(M, I) \longmapsto \mathrm{fst}(I) M} \quad \overline{\mathrm{vproj}_1(N, I) \longmapsto N} \end{array}$$

Figure 3.1: Additional operational semantics for cubical type theory

# Generic

$$\frac{A \longmapsto A'}{\mathrm{coe}_{x.A}^{r \to s}(M) \longmapsto \mathrm{coe}_{x.A'}^{r \to s}(M)} \quad \frac{A \longmapsto A'}{\mathrm{hcom}_A^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto \mathrm{hcom}_{A'}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i})}$$

# Functions

$$\frac{\overline{\mathrm{coe}_{x.(a:A) \to B}^{r \to s}(F) \longmapsto \lambda a. \mathrm{coe}_{x.B[\mathrm{coe}_{x.A}^{s \to x}(a)/a]}^{r \to s}(F(\mathrm{coe}_{x.A}^{s \to r}(a)))}}{\overline{\mathrm{hcom}_{(a:A) \to B}^{r \to s}(F; \overline{\xi_i \hookrightarrow x.G_i}) \longmapsto \lambda a. \mathrm{hcom}_B^{r \to s}(F a; \overline{\xi_i \hookrightarrow x.G_i a})}$$

# Paths

$$\frac{\overline{\mathrm{coe}_{x.\mathrm{Path}(y.A,M_0,M_1)}^{r \to s}(P) \longmapsto \lambda^{\mathbb{I}}y. \mathrm{com}_{x.A}^{r \to s}(P; y \equiv 0 \hookrightarrow x.M_0, y \equiv 1 \hookrightarrow x.M_1)}}{\overline{\mathrm{hcom}_{\mathrm{Path}(y.A,M_0,M_1)}^{r \to s}(P; \overline{\xi_i \hookrightarrow x.Q_i})}} \longmapsto \lambda^{\mathbb{I}}y. \mathrm{hcom}_A^{r \to s}(P y; \overline{\xi_i \hookrightarrow x.Q_i} y, y \equiv 0 \hookrightarrow \_M_0, y \equiv 1 \hookrightarrow \_M_1)}$$

Figure 3.2: Selected rules for coercion and homogeneous composition