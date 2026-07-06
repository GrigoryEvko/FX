5.2. CARTESIAN FIBRATIONS

fits in the sequence of pushouts:

$$\begin{array}{c} [0] \xrightarrow{i_0^+} [1]^{\sharp} \times \{0\} \\ i_0^- \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^{\sharp} \longleftrightarrow [1]^{\sharp} \vee [1]^{\sharp} \xleftarrow{\nabla} [1]^{\sharp} \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^{\sharp} \times [1]^{\sharp} \xleftarrow{\quad} [1]^{\sharp} \vee [1]^{\sharp} \end{array}$$

According to lemma 5.2.1.21, $p$ has the unique right lifting property against $\nabla : [1]^{\sharp} \to [1]^{\sharp} \vee [1]^{\sharp}$ and so also against $[1]^{\sharp} \times \{0\} \to [1]^{\sharp} \times [1]^{\sharp}$. This concludes the proof of the implication $(4) \Rightarrow (1)$. We show similarly $(4)' \Rightarrow (1)'$.

Eventually, the equivalences $(1) \Rightarrow (5)$ and $(1)' \Rightarrow (5)'$ are a consequence of proposition 5.2.1.12 and of the implications $(1) \Rightarrow (4)$ and $(1)' \Rightarrow (4)'$. The implications $(5) \Rightarrow (4)$ and $(5)' \Rightarrow (4)'$ are a consequence of the implications $(1)' \Rightarrow (4)'$ and $(1) \Rightarrow (4)$ applied to the morphisms $\hom_X(x, y) \to \hom_Y(px, py)$ for all objects $x, y$. $\square$

**Corollary 5.2.1.28.** *A morphism $p : X \to A^{\sharp}$ is a left cartesian fibration if and only if for any globular sum $b$ and morphism $j : b \to A$, $j^*p$ is a left cartesian fibration over $b^{\sharp}$.*

*Proof.* This is a direct consequence of the equivalence between conditions (1) and (3) of theorem 5.2.1.26, and the fact that the codomains of marked trivializations and the codomains of morphisms of $F_g$ are marked globular sums. $\square$

### 5.2.2 Cartesian fibration are exponentiable

We recall that a marked globular sum is a marked $(\infty, \omega)$-category whose underlying $(\infty, \omega)$-category is a globular sum and such that for any pair of integers $k \le n$, and any pair of $k$-composable $n$-cells $(x, y)$, $x \circ_k y$ is marked if and only if $x$ and $y$ are marked.

A morphism $i : a \to b$ between marked globular sums is globular if the morphism $i^{\sharp}$ is globular.

A globular morphism $i$ between marked globular sums is then a discrete Conduché functor, which implies according to proposition 5.1.1.29 that the functor $i^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/b} \to (\infty, \omega)\text{-cat}_{\mathrm{m}/a}$ preserves colimits.

**5.2.2.1.** Let $b$ be a globular sum and $f : X \to b^{\sharp}$ a morphism. We say that $f$ is $b$-exponentiable if the canonical morphism

$$\underset{i: \mathrm{Sp}_b^{\sharp}}{\operatorname{colim}} i^* f \to f$$

is an equivalence.

271