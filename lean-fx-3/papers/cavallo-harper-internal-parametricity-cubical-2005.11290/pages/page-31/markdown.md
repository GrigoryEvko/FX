Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:31

Proof. By Lemma 1.3, it suffices to construct a term when $P$ is a constant path $\lambda^{\mathbb{I}}_{-}M \in \mathsf{Path}_A(M, M)$, in which case we have $\lambda^{\mathbb{I}}_{-} \lambda^{\mathbb{I}}_{-} M \in \mathsf{Path}_{\mathsf{Path}_A(M, M)}(\lambda^{\mathbb{I}}_{-} M, \lambda^{\mathbb{I}}_{-} M)$. $\square$

The smash product has a functorial action on pointed functions, which we define as follows.

Definition 3.24. Given $f_*: A_* \to C_*$ and $g_*: B_* \to D_*$, we inductively define a map $f_* \wedge g_* \in A_* \wedge B_* \to C_* \wedge D_*$ as follows.

$$
\begin{array}{l}
(f_* \wedge g_*)(\langle\langle a, b \rangle\rangle) \quad := \quad \langle\langle f a, g b \rangle\rangle \\
(f_* \wedge g_*)(\circledast^{\mathsf{L}}) \quad := \quad \circledast^{\mathsf{L}} \\
(f_* \wedge g_*)(\circledast^{\mathsf{R}}) \quad := \quad \circledast^{\mathsf{R}} \\
(f_* \wedge g_*)(\mathsf{spoke}^{\mathsf{L}}(b, y)) \quad := \quad \mathsf{conc-inv}_{C_* \wedge D_*}^{y, 0}(\mathsf{spoke}^{\mathsf{L}}(g b, y), z.\langle\langle f_0 @ z, g b \rangle\rangle) \\
(f_* \wedge g_*)(\mathsf{spoke}^{\mathsf{R}}(a, y)) \quad := \quad \mathsf{conc-inv}_{C_* \wedge D_*}^{y, 0}(\mathsf{spoke}^{\mathsf{R}}(y, f a), z.\langle\langle f a, g_0 @ z \rangle\rangle)
\end{array}
$$

We now prove the graph lemma: that there is a map from the smash product of two $\mathsf{Gr}^*$-types to the $\mathsf{Gr}$-type corresponding to the smash of their underlying functions. We expect that this map is in fact an isomorphism and that a similar principle holds for $\mathsf{Gel}$-types more generally, but such results are not necessary here.

Lemma 3.25 (Graph Lemma for $\wedge$). For any $\boldsymbol{r} \in \mathbf{I}$, there is a map

$$
\wedge\text{-graph}_\boldsymbol{r} \in \mathsf{Gr}_\boldsymbol{r}^*(A_*, C_*, f_*) \wedge \mathsf{Gr}_\boldsymbol{r}^*(B_*, D_*, g_*) \to \mathsf{Gr}_\boldsymbol{r}(A_* \wedge B_*, C_* \wedge D_*, f_* \wedge g_))
$$

equal to the identity function on $A_* \wedge_* B_*$ when $\boldsymbol{r} = \mathbf{0}$ and on $C_* \wedge_* D_*$ when $\boldsymbol{r} = \mathbf{1}$.

Proof. We define the map by induction on the smash product in the domain.

\(\triangleright\) Case \(\langle \langle m,n\rangle \rangle\) : We test whether \(\pmb{r}\) is a constant or variable using extent. In the constant cases, we return \(\langle \langle m,n\rangle \rangle\) . In the case \(\pmb{r}\) is a variable \(\pmb{x}\) , we learn that \(m\) and \(n\) are the instantiation at \(\pmb{x}\) of bridges over their types; by GEL- \(\eta\) , they are of the form \(m = \mathsf{gel}_{\pmb{x}}(a,c,p)\) and \(n = \mathsf{gel}_{\pmb{x}}(b,d,q)\) . We return \(\mathsf{gel}_{\pmb{x}}(\langle \langle a,b\rangle \rangle ,\langle \langle c,d\rangle \rangle ,\lambda^{\mathbb{I}}z.\langle \langle p@\mathcal{Y},q@\mathcal{Y}\rangle \rangle)\)
\(\triangleright\) Case \(\circledast^{\mathsf{L}}\) : We return \(\mathsf{gel}_{\pmb{r}}(\circledast^{\mathsf{L}},\circledast^{\mathsf{L}},\lambda^{\mathbb{I}}_{-}\circledast^{\mathsf{L}})\)
\(\triangleright\) Case \(\circledast^{\mathsf{R}}\) : Symmetric to \(\circledast^{\mathsf{L}}\)
\(\triangleright\) Case \(\mathsf{spoke}^{\mathsf{L}}(n,y)\): We test whether \(\boldsymbol{r}\) is a constant or variable using extent. In the constant cases, we return \(\mathsf{spoke}^{\mathsf{L}}(n,y)\). In the case \(\boldsymbol{r}\) is a variable \(\boldsymbol{x}\), we learn that \(n\) is the instantiation at \(\boldsymbol{x}\) of a bridge; by GEL-\(\eta\), it is of the form \(n = \mathsf{gel}_{\boldsymbol{x}}(b,d,q)\). We return \(\mathsf{gel}_{\boldsymbol{x}}(\mathsf{spoke}^{\mathsf{L}}(b,y),\mathsf{spoke}^{\mathsf{L}}(d,y),\lambda^{\mathbb{I}}z,\dots)\), where \(\dots\) is the following composite.

$$
\mathsf{hcom}_{C_* \wedge D_*}^{1 \rightharpoonup 0} \left( \begin{array}{c c c c} & y = 0 & \hookrightarrow & \_\cdot \circledast^{\mathsf{L}} \\ \mathsf{spoke}^{\mathsf{L}}(q @ z, y); & y = 1 & \hookrightarrow & w.\langle\langle \mathsf{connect}_A(f_0) @ z @ w, q @ z \rangle\rangle \\ & z = 0 & \hookrightarrow & w.\mathsf{conc-inv}_{C_* \wedge D_*}^{y,w}(\mathsf{spoke}^{\mathsf{L}}(g b, y), z.\langle\langle f_0 @ z, g b \rangle\rangle) \\ & z = 1 & \hookrightarrow & \_\cdot \mathsf{spoke}^{\mathsf{L}}(d, y) \end{array} \right)
$$

$\triangleright$ Case $\mathsf{spoke}^{\mathsf{R}}(m, y)$: Symmetric to $\mathsf{spoke}^{\mathsf{L}}(n, y)$.

When $\boldsymbol{r}$ is a constant, the resulting function simplifies to the $\eta$-expansion of the identity function on $A_* \wedge B_*$. By a simple induction on $A_* \wedge B_*$, the $\eta$-expansion is path-equal to the identity function. We may therefore apply an $\mathsf{hcom}$ to adjust the boundary and obtain a function that is exactly the identity when $\boldsymbol{r} = \mathbf{0}$ or $\boldsymbol{r} = \mathbf{1}$. $\square$

Finally, we use the fact that $\mathsf{bool}_* \wedge \mathsf{bool}_*$ is isomorphic to $\mathsf{bool}_*$. This is a consequence of more general facts—that $\mathsf{bool}_*$ is a unit for the smash product, or alternatively that $(1 + X) \wedge (1 + Y) \simeq 1 + (X \times Y)$ when we take 1 for each basepoint—but we prove the