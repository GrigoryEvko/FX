Iterated smash products

205

- Case $\langle\langle\mathrm{tt},\mathrm{tt}\rangle\rangle$: Reflexivity.

- Case $\langle\langle\mathrm{tt},\mathrm{ff}\rangle\rangle$:

$$\lambda^{\ddagger}y.\mathrm{hcom}_{\mathrm{Bool},\wedge\mathrm{Bool},}^{0\to 1}(\mathrm{spoke}^{\mathrm{L}}(\mathrm{tt},y);y\equiv 0\hookrightarrow x.\mathrm{spoke}^{\mathrm{L}}(\mathrm{ff},x),y\equiv 1\hookrightarrow\dots\langle\langle\mathrm{tt},\mathrm{tt}\rangle\rangle).$$

- Case $\langle\langle\mathrm{ff},\mathrm{ff}\rangle\rangle$: Reflexivity.

- Case $\circledast^{\mathrm{L}}$: $\lambda^{\ddagger}y.\mathrm{spoke}^{\mathrm{L}}(\mathrm{tt},y)$.

- Case $\mathrm{spoke}^{\mathrm{L}}(\mathrm{tt},x)$: $\mathrm{cnx}_{\mathrm{Bool},\wedge\mathrm{Bool},}(\lambda^{\ddagger}y.\mathrm{spoke}^{\mathrm{L}}(\mathrm{tt},y))x$.

- Case $\mathrm{spoke}^{\mathrm{L}}(\mathrm{ff},x)$:

$$\lambda^{\ddagger}y.\mathrm{hcom}_{\mathrm{Bool},\wedge\mathrm{Bool},}^{0\to x}(\mathrm{spoke}^{\mathrm{L}}(\mathrm{tt},y);y\equiv 0\hookrightarrow x.\mathrm{spoke}^{\mathrm{L}}(\mathrm{ff},x),y\equiv 1\hookrightarrow\dots\langle\langle\mathrm{tt},\mathrm{tt}\rangle\rangle).$$

The cases for $\langle\langle\mathrm{tt},\mathrm{ff}\rangle\rangle$, $\circledast^{\mathrm{R}}$, and $\mathrm{spoke}^{\mathrm{R}}$ are obtained by taking the cases for $\langle\langle\mathrm{ff},\mathrm{tt}\rangle\rangle$, $\circledast^{\mathrm{L}}$, and $\mathrm{spoke}^{\mathrm{L}}$ respectively and replacing $\mathrm{spoke}^{\mathrm{L}}$ with $\mathrm{spoke}^{\mathrm{R}}$ everywhere. $\square$

Finally, we need part of a characterization of bridges across smash product types. For our purposes, we only need to analyze bridges across $x.(\mathrm{Gr}_{x}(A_{*},C_{*},f_{*})\wedge\mathrm{Gr}_{x}(B_{*},D_{*},g_{*}))$; we also do not need a full isomorphism, only a map in one direction.

**Lemma 10.5.8 (Graph Lemma for $\wedge$)**. For any $r:\mathbf{I}$, there is a map

$$\wedge\text{-graph}_{r}\in\mathrm{Gr}_{r}(A_{*},C_{*},f_{*})\wedge\mathrm{Gr}_{r}(B_{*},D_{*},g_{*})\to\mathrm{Gr}_{r}(A_{*}\wedge B_{*},C_{*}\wedge D_{*},f_{*}\wedge g_{*})$$

equal to the identity function on $A_{*}\wedge B_{*}$ when $r=\mathbf{0}$ and on $C_{*}\wedge D_{*}$ when $r=\mathbf{1}$.

*Proof.* We define the map by induction on the smash product in the domain.

- Case $\langle\langle m,n\rangle\rangle$: We test whether $r$ is a constant or variable using extent. In the constant cases, we return $\langle\langle m,n\rangle\rangle$. In the case $r$ is a variable $x$, we learn that $m$ and $n$ are the instantiation at $x$ of bridges over their types; by uniqueness, they are of the form $m=\mathrm{gel}_{x}(a,c,p)$ and $n=\mathrm{gel}_{x}(b,d,q)$. We return $\mathrm{gel}_{x}(\langle\langle a,b\rangle\rangle,\langle\langle c,d\rangle\rangle,\lambda^{\ddagger}z.\langle\langle py,qy\rangle\rangle)$.

- Case $\circledast^{\mathrm{L}}$: We return $\mathrm{gel}_{r}(\circledast^{\mathrm{L}},\circledast^{\mathrm{L}},\lambda^{\ddagger}\dots\circledast^{\mathrm{L}})$.

- Case $\circledast^{\mathrm{R}}$: Symmetric to $\circledast^{\mathrm{L}}$.

- Case $\mathrm{spoke}^{\mathrm{L}}(n,y)$: We test whether $r$ is a constant or variable using extent. In the constant cases, we return $\mathrm{spoke}^{\mathrm{L}}(n,y)$. In the case $r$ is a variable $x$, we learn that $n$ is the instantiation at $x$ of a bridge; by uniqueness, it is of the form $n=\mathrm{gel}_{x}(b,d,q)$. We return $\mathrm{gel}_{x}(\mathrm{spoke}^{\mathrm{L}}(b,y),\mathrm{spoke}^{\mathrm{L}}(d,y),\lambda^{\ddagger}z.\dots)$, where $\dots$ is the following composite.

$$\mathrm{hcom}_{C_{*}\wedge D_{*}}^{1\to 0}\left(\mathrm{spoke}^{\mathrm{L}}(qz,y);\begin{array}{l} y\equiv 0 \hookrightarrow \dots\circledast^{\mathrm{L}} \\ y\equiv 1 \hookrightarrow w.\langle\langle\mathrm{cnx}_{A}(f_{0})zw,qz\rangle\rangle \\ z\equiv 0 \hookrightarrow w.\mathrm{conc-inv}_{C_{*}\wedge D_{*}}^{y,w}(\mathrm{spoke}^{\mathrm{L}}(gb,y),z.\langle\langle f_{0}z,gb\rangle\rangle) \\ z\equiv 1 \hookrightarrow \dots\mathrm{spoke}^{\mathrm{L}}(d,y) \end{array}\right)$$