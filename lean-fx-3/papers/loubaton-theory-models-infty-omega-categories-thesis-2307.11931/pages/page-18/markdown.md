Introduction

by $(\gamma, n)$-cat the $(\infty, 1)$-category of $(\gamma, n)$-categories. Since we have not given a precise definition of $\Theta$, we cannot explicitly state these conditions, but we will try to explain their essence.

**Segal conditions.** As the diagrams given in the examples suggest, every globular sum is a colimit of globes. For instance, $a_2$ is the colimit of the following diagram

$$\begin{array}{c} \mathbf{D}_2 \\ i_1^+ \uparrow \\ \mathbf{D}_1 \xleftarrow{i_0^+} \mathbf{D}_0 \xrightarrow{i_0^-} \mathbf{D}_2 \\ i_1^- \downarrow \\ \mathbf{D}_3 \end{array}$$

A functor $X : \Theta_n^{op} \to \gamma$ satisfies the *Segal conditions* if it sends these colimits to limits. For instance, the presheaf $X$ must send $a_2$ to the limit of the diagram

$$\begin{array}{c} X(\mathbf{D}_2) \\ \pi_1^+ \downarrow \\ X(\mathbf{D}_1) \xrightarrow{\pi_0^+} X(\mathbf{D}_0) \xleftarrow{\pi_0^-} X(\mathbf{D}_2) \\ \pi_1^- \uparrow \\ X(\mathbf{D}_3) \end{array}$$

The morphisms $X(f_0)$ and $X(f_1)$ can then be interpreted as compositions and the morphism $X(f_3)$ as a unit.

**Completeness conditions.** Let $X : \Theta_n^{op} \to \gamma$ be a functor satisfying the Segal conditions. Given an integer $k \le n$, we have two notions of equivalence on the $k$-cells of $X$, i.e. the morphisms $1 \to X(\mathbf{D}_k)$. The first comes from the canonical equivalence provided by the $\infty$-groupoid $\operatorname{Hom}(1, X(\mathbf{D}_k))$, and the second is more categorical and identifies *isomorphic* elements, i.e. $k$-cells $a, b$ such that there exists $(k+1)$-cells $f : a \to b$, $g : b \to a$ and equivalences

$$g \circ_k f \sim id_a \qquad \text{and} \qquad f \circ_k g \sim id_b.$$

The presheaf $X$ satisfies the completeness condition if these two notions of equivalence coincide. Thus, *groupoids*, i.e., $(\gamma, n)$-categories in which all $k$-cells are equivalent to the identity of their source (or target), correspond to constant functors $\Theta^{op} \to \gamma$. The datum of the $(\infty, 1)$-category $\gamma$ can be understood as a *choice of a notion of groupoid*.

When $\gamma$ is the category of sets, the $(\gamma, n)$-categories will simply be denoted as $(0, n)$-categories, and when $\gamma$ is the $(\infty, 1)$-category of spaces, they will be denoted as $(\infty, n)$-categories.

8