Bridge-discrete types 199

The bridge-discrete universe even inherits univalence and relativity. This means in particular that we can use internal parametricity to characterize functions out of the bridge-discrete universe. For example, we can show that the “bridge discrete Church boolean” type, $(A : \text{U}_{\text{bdisc}}) \rightarrow \text{fst}(A) \rightarrow \text{fst}(A) \rightarrow \text{fst}(A)$, is also isomorphic to Bool.

**Theorem 10.3.9.** $\text{U}_{\text{bdisc}}$ is univalent, in the sense that $\text{Path}(\text{U}_{\text{bdisc}}, A, B)$ is isomorphic to $\text{fst}(A) \simeq \text{fst}(B)$ by way of the coercion isomorphism map for any $A, B : \text{U}_{\text{bdisc}}$.

*Proof.* By univalence of U, it is equivalent to show that the projection function from $\text{Path}(\text{U}_{\text{bdisc}}, A, B)$ to $\text{Path}(\text{U}, \text{fst}(A), \text{fst}(B))$ is an isomorphism. This follows quickly from **Lemma 3.2.4** and the fact that $\text{IsBDisc}(C)$ is a proposition for any $C : \text{U}$. $\square$

Relativity comes down to the closure of the bridge-discrete universe under Gel-types.

**Theorem 10.3.10.** Let $A, B$ type and $a : A, b : B \gg R$ type be given. If $A, B$ are bridge-discrete and $R$ is pointwise bridge-discrete, then $\text{Gel}_x(A, B, a.b.R)$ is bridge-discrete for any fresh $x$.

*Proof.* Set $G_x := \text{Gel}_x(A, B, a.b.R)$. We aim to show that paths and bridges from $g_0$ to $g_1$ in $G_x$ are isomorphic for any $g_0, g_1 : G_x$. By applying extent, it suffices to show this is the case when either $x$ is an endpoint or $g_0$ and $g_1$ are points on bridges. When $x$ is an endpoint, we apply the $\text{loosen}_A$ or $\text{loosen}_B$ isomorphism accordingly. For the remaining case, we need

$$\text{Path}(G_x, q_0 x, q_1 x) \simeq \text{Bridge}(G_x, q_0 x, q_1 x)$$

for all $q_0 : \text{Bridge}(x.G_x, a_0, b_0)$ and $q_1 : \text{Bridge}(x.G_x, a_1, b_1)$, coherently with the endpoint cases. Now, by **Lemma 10.2.2**, it suffices to construct an isomorphism of the following type for any $p \in \text{Path}(A, a_0, a_1)$ and $p' \in \text{Path}(B, b_0, b_1)$.

$$\begin{aligned} \text{Bridge}(x.\text{Path}(G_x, q_0 x, q_1 x), p, p') \\ \simeq \\ \text{Bridge}(x.\text{Bridge}(G_x, q_0 x, q_1 x), \text{loosen}_A p, \text{loosen}_B p') \end{aligned}$$

By **Lemma 3.2.3**, we can assume that the paths $p$ and $p'$ are reflexive; together with the fact that loosen takes reflexive paths to reflexive bridges, this simplifies our goal to the following.

$$\begin{aligned} \text{Bridge}(x.\text{Path}(G_x, q_0 x, q_1 x), \lambda^\sharp \dots a_0, \lambda^\sharp \dots b_0) \\ \simeq \\ \text{Bridge}(x.\text{Bridge}(G_x, q_0 x, q_1 x), \lambda^\sharp \dots a_0, \lambda^\sharp \dots b_0) \end{aligned}$$