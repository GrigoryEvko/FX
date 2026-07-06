206

Programming with parametricity

- Case spoke$^{\text{R}}(m, y)$: Symmetric to spoke$^{\text{L}}(n, y)$.

When $r$ is a constant, the resulting function simplifies to a term path-equal to the identity function on $A_* \wedge B_*$. We may therefore apply an hcom to adjust the boundary and obtain a function that is exactly the identity when $r = 0$ or $r = 1$. $\square$

The following lemma represents the sole use of parametricity in the final proof.

**Lemma 10.5.9 (Workhorse lemma).** Let $F \in (A_*, B_* : \cup_*) \to A \to B \to A_* \wedge_* B_*$. Then $F$ is path equal to one of either $(\lambda_-, \lambda_--, \lambda a, \lambda b, \langle\langle a, b \rangle\rangle)$ or $(\lambda A_*, \lambda B_*, \lambda_--, \lambda_-, \langle\langle a_0, b_0 \rangle\rangle)$.

*Proof.* We show that $F$ is determined by the value of $F \text{Bool}_* \text{Bool}_* \text{ff ff}$. Let $A_* : \cup_*$, $B_* : \cup_*$, $a : A$, and $b : B$ be given.

We have a pointed function $[a]_* \in \text{Bool}_* \to A_*$ sending tt to $a_0$ and ff to $a$, likewise $[b]_* \in \text{Bool}_* \to B_*$ sending tt to $b_0$ and ff to $b$. Abstract a fresh bridge variable $x : \mathbf{I}$. We abbreviate $G_*^a := \text{Gr}_x(\text{Bool}_*, A_*, [a]_*)$ and $G_*^b := \text{Gr}_x(\text{Bool}_*, B_*, [b]_*)$. Applying $F$ at $G_*^a$ and $G_*^b$, we have the following.

$$F G_*^a G_*^b (\text{gel}_x(\text{ff}, a, \lambda_{-}^\text{I}, a)) (\text{gel}_x(\text{ff}, b, \lambda_{-}^\text{I}, b)) \in G_*^a \wedge G_*^b$$

At $x = 0$, this term is $F \text{Bool}_* \text{Bool}_* \text{ff ff}$, while at $x = 1$ it is $F A_* B_* a b$. Now we apply the Graph Lemma to obtain a term in $\text{Gr}_x(\text{Bool}_* \wedge \text{Bool}_*, A_* \wedge B_*, [a]_* \wedge [b]_*)$ with the same boundary. Finally, we apply ungel to extract a path from $([a]_* \wedge [b]_*) (F \text{Bool}_* \text{Bool}_* \text{ff ff})$ to $F A_* B_* a b$. We thereby conclude that $F$ is the pairing function if $F \text{Bool}_* \text{Bool}_* \text{ff ff}$ is $\langle\langle \text{ff}, \text{ff} \rangle\rangle$ and the constant function if it is $\langle\langle \text{tt}, \text{tt} \rangle\rangle$; by Lemma 10.5.7, we are in one of these two cases. $\square$

**Corollary 10.5.10.** $(A_*, B_* : \cup_*) \to A \to B \to A_* \wedge_* B_*$ is a set, which is to say that every path type in this type is a proposition.

*Proof.* Lemma 10.5.9 shows that the type is isomorphic to Bool, which is a set. $\square$

This is everything we need to prove the final result.

*Proof (of Theorem 10.5.2).* Let $F_* \in (A_*, B_* : \cup_*) \to A_* \wedge_* B_* \to A_* \wedge_* B_*$ be given. To characterize $F_*$, we need to characterize its behavior on each constructor of $A_* \wedge B_*$ as well as the proof that it preserves the basepoint of $A_* \wedge_* B_*$.

First, by Lemma 10.5.9, we know that $\lambda a, \lambda b, F A_* B_* \langle\langle a, b \rangle\rangle$ is either pairing or constant. The values of $F A_* B_* \otimes^\text{L}$ and $F A_* B_* \otimes^\text{R}$ must be path-equal to $\otimes^\text{L}$ and $\otimes^\text{R}$ respectively, as $F$ is basepoint-preserving and $\otimes^\text{L} (\otimes^\text{R})$ is connected to the basepoint by spoke$^\text{L}(b_0, -)$ (spoke$^\text{R}(a_0, -)$).