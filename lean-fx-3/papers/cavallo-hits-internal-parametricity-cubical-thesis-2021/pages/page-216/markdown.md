204

Programming with parametricity

Lemma 10.5.4 (Join connection). For any $a_0, a_1 : A$ and $p : \text{Path}(A, a_0, a_1)$, we have a term as follows, a square with $p$ on the two "0" sides and reflexivity on the two "1" sides.

$$\text{cnx}_A(p) \in \text{Path}(x.\text{Path}(A, px, a_1), p, \lambda^\mathbb{I}_{-}, a_1)$$

Proof. By J for paths (Lemma 3.2.3), it suffices to construct such a term in the case that $p$ is a reflexive path $\lambda^\mathbb{I}_{-}, a$, in which case we may take $\lambda^\mathbb{I}_{-}, \lambda^\mathbb{I}_{-}, a$. $\square$

Our uses of parametricity for this theorem are limited to cases where the relation is the graph of a function, so we introduce some notation for this case.

Notation 10.5.5. Given $f : A \to B$, write $\text{Gr}_r(A, B, f) := \text{Gel}_r(A, B, a.b.\text{Path}(B, fa, b))$. Given $f_* : A_* \to B_*$, define $\text{Gr}_r(A_*, B_*, f_*) := \langle \text{Gr}_r(A, B, f), \text{gel}_r(a_0, b_0, f_0) \rangle \in \text{U}_*$.

The first property we need of the smash product is that it acts on pointed functions in either argument.

Definition 10.5.6. Given pointed functions $f_* : A_* \to C_*$ and $g_* : B_* \to D_*$, we define a map $f_* \wedge g_* \in (A_* \wedge B_*) \to (C_* \wedge D_*)$ by smash product elimination as follows.

$$(f_* \wedge g_*) s := \left[ \begin{array}{l} \text{case } s \text{ of} \\ | \langle \langle a, b \rangle \rangle \mapsto \langle \langle f a, g b \rangle \rangle \\ | \otimes^L \mapsto \otimes^L \\ | \text{spoke}^L(b, y) \mapsto \text{conc-inv}_{C_* \wedge D_*}^{y, 0}(\text{spoke}^L(g b, y), z. \langle \langle f_0 z, g b \rangle \rangle) \\ | \otimes^R \mapsto \otimes^R \\ | \text{spoke}^R(a, x) \mapsto \text{conc-inv}_{C_* \wedge D_*}^{x, 0}(\text{spoke}^R(f a, y), z. \langle \langle f a, g_0 z \rangle \rangle) \end{array} \right]$$

This map is basepoint-preserving; we write $f_* \wedge_* g_* := \langle f_* \wedge g_*, \lambda^\mathbb{I}x. \langle \langle f_0 x, g_0 x \rangle \rangle$ for the pointed function.

The second is that $\text{Bool}_* := \langle \text{Bool}, \text{tt} \rangle$ is a unit for the smash product; actually, we only need the special case $\text{Bool}_* \wedge \text{Bool}_* \simeq \text{Bool}$.

Lemma 10.5.7 (Smash of booleans). $\text{Bool}_* \wedge \text{Bool}_*$ is isomorphic to $\text{Bool}$; in particular, any element of $\text{Bool}_* \wedge \text{Bool}_*$ is path-equal to either $\langle \langle \text{tt}, \text{tt} \rangle \rangle$ or $\langle \langle \text{ff}, \text{ff} \rangle \rangle$.

Proof. In one direction, we define $F \in \text{Bool} \to \text{Bool}_* \wedge \text{Bool}_*$ to send $\text{tt}$ to $\langle \langle \text{tt}, \text{tt} \rangle \rangle$ and $\text{ff}$ to $\langle \langle \text{ff}, \text{ff} \rangle \rangle$. In the other, we define $G \in \text{Bool}_* \wedge \text{Bool}_* \to \text{Bool}$ to send $\langle \langle \text{ff}, \text{ff} \rangle \rangle$ to $\text{ff}$ and all other constructors to $\text{tt}$. Clearly $\lambda b. G(Fb)$ is the identity. For the other inverse condition, we show $(s: \text{Bool}_* \wedge \text{Bool}_*) \to \text{Path}(\text{Bool}_* \wedge \text{Bool}_*, s, F(Gs))$ by smash product induction as follows.