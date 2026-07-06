42

E. Cavallo and C. Sattler

Definition 5.12 For any $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ and $n \in \mathbb{N}$, the $<n$-skeleton map for $f$ is the Leibniz weighted colimit

$$(\mathrm{sk}_{<n}\mathbf{R} \mapsto \mathscr{L}\mathbf{R}) \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f.$$

We write $\mathrm{sk}_{<n}f \in \mathrm{PSh}(\mathbf{R})$ for the domain of this map, which we call the $<n$-skeleton of $f$; its codomain is $Y$. For $Y \in \mathrm{PSh}(\mathbf{R})$, we write $\mathrm{sk}_{<n}Y$ for the $n$-skeleton of the map $0 \mapsto Y$.

Note that the $<0$-skeleton map is $(0 \mapsto \mathscr{L}\mathbf{R}) \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f \cong \mathscr{L}\mathbf{R} \circledast_{\mathbf{R}^{\mathrm{op}}} f \cong f$. For each $m \leq n \in \mathbb{N}$, the inclusion $\mathrm{sk}_{<m}\mathbf{R} \mapsto \mathrm{sk}_{<n}\mathbf{R}$ induces a morphism $\mathrm{sk}_{<m}f \to \mathrm{sk}_{<n}f$ by functoriality of weighted colimits, and the fact that $\mathscr{L}\mathbf{R}$ is the union of the subfunctors $\mathrm{sk}_{<n}\mathbf{R}$ implies that $Y \cong \mathrm{colim}_{n \in \mathbb{N}} \mathrm{sk}_{<n}f$. Thus we have a natural decomposition of $f$ as the transfinite composite $\mathrm{sk}_{<0}f \to \mathrm{sk}_{<1}f \to \mathrm{sk}_{<2}f \to \cdots$ where we may compute $\mathrm{sk}_{<n}f \cong X \sqcup_{\mathrm{sk}_{<n}X} \mathrm{sk}_{<n}Y$. The chain of skeleta may be further decomposed in terms of latching maps:

Definition 5.13 Given $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ and $r \in \mathbf{R}$, define the latching map $\widehat{\ell}_r f \in \mathbf{Set}^\to$ for $f$ at $r$ by the Leibniz weighted colimit

$$\widehat{\ell}_r f := \partial_r \mathbf{R} \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f.$$

The codomain of this map is $Y_r$; we write $L_r f$ for its domain and call this the latching object for $f$ at $r$.

We write $\widehat{\ell}_r Y$ and $L_r Y$ for the latching map and object of $0 \mapsto Y$ at $r$. For general $f: X \to Y$, we can calculate that $L_r f \cong X_r \sqcup_{L_r X} L_r Y$ and $\widehat{\ell}_r f \cong [f_r, L_r f]$. It is convenient to have notation for the collected $\mathbf{R}[n]$-sets of latching maps at a given degree:

Definition 5.14 Given $f: X \to Y$ and $n \in \mathbb{N}$, we define the $n$th latching map of $f$ by $\widehat{\ell}_n f := \partial_n \mathbf{R} \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f$. We write $L_n f \in \mathrm{PSh}(\mathbf{R}[n])$ for its domain and $f_n \in \mathrm{PSh}(\mathbf{R}[n])$ for its codomain.

These maps are assembled from the latching maps at the individual objects of degree $n$: we have $(\widehat{\ell}_n f)_r \cong \widehat{\ell}_r f$ for each $r \in \mathbf{R}[n]$.

We can now exhibit the maps between successive $<n$-skeleta as pushouts of Leibniz weighted colimits of boundary inclusions and latching maps. The induced decomposition of a map $f$ into a sequential colimit of pushouts of basic maps is what we mean by a cellular presentation of $f$:

2025/10/16 00:43