Bridge-discrete types

197

**Theorem 10.3.7 (Bridges in Bool).** Bool is bridge-discrete.

*Proof.* We define a right inverse to $\text{loosen}_{\text{Bool}} \in \text{Path}(\text{Bool}, b_0, b_1) \to \text{Bridge}(\text{Bool}, b_0, b_1)$ given $b_0, b_1 : \text{Bool}$. We make use of the Gel type for the path relation in Bool.

$$x : \mathbf{I} \gg G_x := \text{Gel}_x(\text{Bool}, \text{Bool}, \text{Path}(\text{Bool}, -, -)) \text{ type}$$

This type has two canonical elements corresponding to the reflexive proofs of equality in Bool, $t_x := \text{gel}_x(\text{tt}, \text{tt}, \lambda^\mathbb{I}_{-}, \text{tt})$ and $f_x := \text{gel}_x(\text{ff}, \text{ff}, \lambda^\mathbb{I}_{-}, \text{ff})$. We first define an auxiliary map $F_x \in \text{Bool} \to G_x$ by case analysis, returning the corresponding reflexivity path in each case.

$$F_x := \lambda b. \text{elim}_{\text{Bool}}(-, G_x; b; t_x, f_x) \in \text{Bool} \to G_x$$

Note we can transform this bridge in a function type into a function from bridges to bridges, then use ungel to extract a path from the resulting bridge over $x.G_x$.

$$F := \lambda p. \text{ungel}(x.F_x(p x)) \in \text{Bridge}(\text{Bool}, b_0, b_1) \to \text{Path}(\text{Bool}, F_0 b_0, F_1 b_1)$$

Modulo the not-quite-correct endpoints of the output, this will be our candidate right inverse. Conversely, we can extract a map $G_x \to \text{Bool}$ from $\text{loosen}_{\text{Bool}}$ using extent.

$$L_x := \lambda g. \text{extent}_x(g; b_0.b_0, b_1.b_1, \dots, q.\text{loosen}_{\text{Bool}}(\text{ungel}(x.q x))) \in G_x \to \text{Bool}$$

To check the inverse condition, we start by checking that $F_x$ is right inverse to $L_x$, constructing a term of the following type.

$$P_x \in (b : \text{Bool}) \to \text{Path}(\text{Bool}, L_x(F_x b), b)$$

Examining $L_x(F_x \text{tt})$, we have the following sequence of equations and paths in Bool.

$$\begin{aligned} L_x(F_x \text{tt}) &= \text{extent}_x(t_x; b_0.b_0, b_1.b_1, \dots, q.\text{loosen}_{\text{Bool}}(\text{ungel}(x.q x))) \\ &= \text{loosen}_{\text{Bool}}(\text{ungel}(x.t_x)) x \\ &= \text{loosen}_{\text{Bool}}(\lambda^\mathbb{I}_{-}, \text{tt}) x \\ &\rightsquigarrow (\lambda^\mathbb{I}_{-}, \text{tt}) x \\ &= \text{tt} \end{aligned}$$

We likewise have a path $L_x(F_x \text{ff}) \rightsquigarrow \text{ff}$, so we can define $P_x$ by case analysis. Finally, we move from bridges of functions to functions of bridges once more, defining the term $\lambda q. \lambda^\mathbb{I} x. P_x(q x)$ of the following type.

$$(q : \text{Bridge}(\text{Bool}, b_0, b_1)) \to \text{Bridge}(x.\text{Path}(\text{Bool}, L_x(F_x q x), q x), P_0 b_0, P_1 b_1)$$