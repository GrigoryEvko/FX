Modal types

255

# Formation

$$\frac{\mu \in \{\mathrm{cc}, \mathrm{dsc}, \mathrm{glo}\}}{\langle \mu \mid A \rangle \mathrm{val}}$$

# Introduction

$$\overline{\mathrm{mod}(M) \mathrm{val}}$$

# Projection

$$\frac{P \longmapsto P'}{\mathrm{unmod}(P) \longmapsto \mathrm{unmod}(P')}$$

$$\overline{\mathrm{unmod}(\mathrm{mod}(M)) \longmapsto M}$$

# Discrete elimination

$$\frac{P \longmapsto P'}{\mathrm{letdisc}(d.B, P, a.N) \longmapsto \mathrm{letdisc}(d.B, P', a.N)}$$

$$\overline{\mathrm{letdisc}(d.B, \mathrm{mod}(M), a.N) \longmapsto N[M/a]}$$

$$\mathrm{letdisc}(d.B, \mathrm{fhcom}^{r \to s}(P; \overrightarrow{\xi_i \hookrightarrow x.P_i}), a.N)$$

$$\longmapsto$$

$$\mathrm{com}^{r \to s}_{x.B[\mathrm{fhcom}^{r \to s}(P; \overrightarrow{\xi_i \hookrightarrow x.P_i})/d]} (\mathrm{letdisc}(d.B, P, a.N); \overrightarrow{\xi_i \hookrightarrow \mathrm{letdisc}(d.B, P_i, a.N)})$$

# Splitting

$$\overline{\mathrm{split}_0(M_0, M_1) \longmapsto M_0}$$

$$\overline{\mathrm{split}_1(M_0, M_1) \longmapsto M_1}$$

Figure 14.4: Operational semantics for modal parametric type theory: formation, introduction, elimination, splitting

Definition 14.4.1. Let $\Psi$ ictx @ $n$ and $\mu : m \to n$. Given a value $(m, \Psi, \mu)$-relation $R$, we define a value $(n, \Psi)$-relation $Mod_\mu(R)$ for $\Psi' \Vdash \psi \in \Psi$.

$$V \approx V' \in Mod_\mu(R)\langle\psi\rangle : \Longleftrightarrow \begin{cases} V = \mathrm{mod}(M) \text{ and } V' = \mathrm{mod}(M') \\ \text{with } M \approx M' \in \Downarrow R[(\psi : \Psi) \otimes \mu] \end{cases}$$

For Glo($A$) and Codisc($A$), the above will be their defining relation. These two types support projection rules that invert the introduction rule, a setup that reflects the status of dsc and glo as right adjoints. As such, the Kan operations for these types are easily implemented: as with functions or products, we unpack the underlying elements of $A$, coerce or compose them, and repackage.