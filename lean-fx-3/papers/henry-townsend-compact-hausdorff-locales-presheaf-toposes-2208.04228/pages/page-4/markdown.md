4

SIMON HENRY AND CHRISTOPHER TOWNSEND

splitting of the category $\mathbf{NDL}_{\mathcal{T}}$. We will use this to understand the category $\mathbf{KRegFrm}_{\mathcal{C}}$, but in order to do so we will need an explicit description of the functor $C_{\mathcal{C}}: \mathbf{NDL}_{\mathcal{C}} \rightarrow \mathbf{NDL}_{\mathcal{C}}$; the next two sections lead up to this explicit description.

### 3. TURNING LAX NATURAL TRANSFORMATION INTO ORDINARY NATURAL TRANSFORMATIONS

In this section we outline a basic categorical construction that relates lax natural transformations between presheaves taking values in an order enriched category, to ordinary natural transformations. In the next section we will show that this construction is closely related to the functor $C_{\mathcal{C}}$.

We will work with order enriched categories; that is, homsets are partially ordered sets (posets) and composition preserves the order. The order relation between morphisms will be denoted $\sqsubseteq$. Universal properties are required to establish order isomorphisms (not just bijections) between the posets of morphisms.

If $F_1, F_2: \mathcal{C}^{op} \rightarrow \mathfrak{K}$ are two order enriched functors between order enriched categories, then a *lax* natural transformation $\phi: F_1 \xrightarrow{\sqsubseteq} F_2$ is a collection of morphisms $\phi_a: F_1(a) \rightarrow F_2(a)$ indexed by objects $a$ of $\mathcal{C}$ such that for any morphism $h: a \rightarrow a'$ of $\mathcal{C}$, $\phi_{a'} F_1(h) \supseteq F_2(h) \phi_a$; i.e.

$$\begin{array}{ccc} F_1(a) & \xrightarrow{\phi_a} & F_2(a) \\ F_1(h) \downarrow & \supseteq & \downarrow F_2(h) \\ F_1(a') & \xrightarrow{\phi_{a'}} & F_2(a') \end{array}$$

We use $[\mathcal{C}^{op}, \mathfrak{K}]^{\sqsubseteq}$ as notation for the order enriched category of presheaves with lax natural transformations between them. The ordering on the lax natural transformation is pointwise.

Recall that a lax limit of an order enriched functor $\mathcal{D}: \mathcal{J} \rightarrow \mathfrak{K}$ is a universal lax cone, where a *lax* cone is collection of morphisms $\pi_j: \lim_{\mathcal{J}} D \rightarrow D(j)$ indexed by object $j$ of $\mathcal{J}$ such that for any morphism $\alpha: i \rightarrow j$ of $\mathcal{J}$, $D(\alpha)\pi_i \sqsubseteq \pi_j$.

**Example 3.1.** The order enriched category of posets, **Pos**, has arbitrary lax limits. Given $D: \mathcal{J} \rightarrow \mathbf{Pos}$,

$$\lim_{\mathcal{J}} D = \{(x_j) \in \prod_{j \in Ob(\mathcal{J})} D(j) | D(\alpha)x_i \leq x_j \ \forall \alpha: i \rightarrow j \in \mathcal{J}\}.$$

Another example is the category of distributive lattices; it is easy to check that lax limits of distributive lattices are created in **Pos**

**Example 3.2.** The category of suplattices (i.e. complete lattices with arbitrary join preserving maps as morphisms), **Sup**, has arbitrary lax limits. They are created in **Pos** with join given pointwise (i.e. $\bigvee_{i \in I} (x_j^i) = (\bigvee_{i \in I} x_j^i)$).

We will only need the existence of lax limits for $\mathcal{J}$ with an initial object.

**Definition 3.3.** *An order enriched category $\mathfrak{K}$ is initial-lax complete if it has a lax limit $\lim_{\mathcal{J}} D$ whenever $\mathcal{J}$ has an initial object.*

The category **NDL** is relatively far from being complete in general, but it does satisfies this condition: