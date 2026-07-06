## B.1 $\kappa$-contextual categories

The discussion in section A.5 on the properties of the syntactic category $\mathbb{C}_T$ can be summarized with the next definition, which is the natural generalization of Cartmell's [Car78] or [KL18]. We present our definition in the same way as in the latter reference. Recall that $\kappa$ is a regular cardinal.

**Definition B.1.** A category $\mathcal{C}$ is said to be a $\kappa$-contextual category if:

1. The objects of $\mathcal{C}$ have grading $Ob(\mathcal{C}) = \coprod_{\lambda < \kappa} Ob_\lambda(\mathcal{C})$. This grading determines the *height* of any object $B \in \mathcal{C}$, which we write as $ht(B)$.
2. There is a terminal object $1 \in \mathcal{C}$, it is unique up to equality and has height 0.
3. There is a wide subcategory $Dis(\mathcal{C})$ with distinguished maps “$\twoheadrightarrow$” called *display morphisms*,
4. The subcategory $Dis(\mathcal{C})$ is closed under transfinite compositions: if we have

$$\cdots \longrightarrow B_3 \longrightarrow B_2 \longrightarrow B_1 \longrightarrow B_0$$

a $\lambda$-sequence of display maps, then there is a unique object $B$ in $Dis(\mathcal{C})$ with height $\lambda$ and for each $\mu \leq \lambda$ a display map $B \twoheadrightarrow B_\mu$ such that for any $\alpha < \lambda$ we have a factorization

$$\begin{array}{c} B \xrightarrow{} B_0 \\ \searrow B_\alpha \end{array}$$

5. The inclusion functor preserves $i : Dis(\mathcal{C}) \hookrightarrow \mathcal{C}$ transfinite compositions.
6. If $A \twoheadrightarrow B$ is an arrow in $Dis(\mathcal{C})$ then $B \in Ob_\mu(\mathcal{C})$ and $A \in Ob_\lambda(\mathcal{C})$ for some ordinals $\lambda, \mu$ with $\mu \leq \lambda$.
7. For any object $A \in Ob_\lambda(\mathcal{C})$ and any $\mu \leq \lambda$ there exists a unique object $B \in Ob_\mu(\mathcal{C})$ and a unique display map $A \twoheadrightarrow B$. The *length* of this display map is the unique ordinal $\alpha$ such that $\lambda = \mu + \alpha$, is such situation, we write $lt(p)$.

111