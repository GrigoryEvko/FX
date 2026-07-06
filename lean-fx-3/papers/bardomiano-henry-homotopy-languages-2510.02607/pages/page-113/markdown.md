*Remark B.4.* It follows from theorem B.1 that for any object $B \in \mathcal{C}$ the map $B \rightarrow 1$ can be decomposed as a transfinite composition of display maps

$$B_\lambda \rightarrow \dots \rightarrow B_1 \rightarrow 1.$$

The length of the decomposition above is given by the degree of $B$. This is what [Car78] calls the tree structure of the category. Whenever we refer to objects in a $\kappa$-contextual category as above, we will emphasize its height by writing $B_\lambda$. Likewise, we will denote the display maps as $p_\alpha : B_\lambda \rightarrow B_\alpha$ for each $\alpha < \lambda$.

The following lemma is a consequence of theorem B.1 and theorem B.4.

**Lemma B.5.** *Let $B \in Ob_\lambda(\mathcal{C})$ such that $\lambda$ is a limit ordinal. Then $B$ itself is a limit object in $\mathcal{C}$.*

*Proof.* From theorem A.32 we obtain a sequence

$$\dots \longrightarrow B_3 \longrightarrow B_2 \longrightarrow B_1 \longrightarrow 1.$$

It follows from Axiom 4 of theorem B.1 that $B$ must be the limit of the sequence. Finally, we use that the inclusion $Dis(\mathcal{C}) \rightarrow \mathcal{C}$ preserve limits. $\square$

**Definition B.6.** Let $\mathcal{C}, \mathcal{D}$ contextual categories. A functor $F : \mathcal{C} \rightarrow \mathcal{D}$ it is called a *contextual functor* if it satisfies the following conditions:

1. $F(Ob_\lambda(\mathcal{C})) \subseteq Ob_\lambda(\mathcal{D})$ for all $\lambda < \kappa$,
2. $F$ restricts to a functor $Dis(\mathcal{C}) \rightarrow Dis(\mathcal{D})$,
3. $F$ preserves canonical pullbacks up to equality, meaning that for any square in $\mathcal{C}$

$$\begin{array}{c} f^*A \xrightarrow{q(f,A)} A \\ f^*p \downarrow \quad \downarrow p \\ C \xrightarrow{f} B \end{array}$$

we have $F(f^*A) = (Ff)^*(FA)$ and $F(q(f,A)) = q(Ff, FA)$.

Since the degree of each object is preserved by a $\kappa$-contextual functor, it makes sense to denote $F(A_\lambda) := F(A)_\lambda$ for $A_\lambda \in \mathcal{C}$. Another piece of notation we can introduce is from the functor $F : Dis(\mathcal{C}) \rightarrow Dis(\mathcal{D})$. Since any display map $p_\alpha : A_\lambda \rightarrow A_\alpha$ is sent to a display map $F(p_\alpha) : F(A)_\lambda \rightarrow F(A)_\alpha$, and the degrees are preserved, we agree to omit $F$ on these maps.

Contextual functors are the morphisms of the category of $\kappa$-contextual categories, which we will denote it as $\kappa$-CON.

113