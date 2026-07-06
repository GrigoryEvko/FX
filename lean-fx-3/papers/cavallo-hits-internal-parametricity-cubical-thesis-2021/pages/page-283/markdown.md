Bridge-discreteness

271

Conversely, we have a function $G_x \to \text{Disc}(A)$ given by loosen and extent, as in the case of Bool.

$$L_x := \lambda g. \text{extent}_x(g; d_0. d_0, d_1. d_1, \dots. q. \text{loosen}_{\text{Disc}(A)} (\text{ungel}(x. q x))) \in G_x \to \text{Disc}(A)$$

We next construct a term $P_x \in (d : \text{Disc}(A)) \to \text{Path}(\text{Disc}(A), L_x(F_x d), d)$ showing that $F_x$ is a right inverse to $L_x$. By parametric elimination for the discrete type, it suffices to show $\text{Path}(\text{Disc}(A), L_x(F_x \text{ mod}(a)), \text{mod}(a))$ for all $(\text{cc} \mid a : A)$. This follows from the following sequence of paths and equations in $\text{Disc}(A)$.

$$\begin{aligned} L_x(F_x (\text{mod}(a))) &= \text{extent}_x(F_x (\text{mod}(a)); d_0. d_0, d_1. d_1, \dots. q. \text{loosen}_{\text{Disc}(A)} (\text{ungel}(x. q x))) \\ &= \text{loosen}_{\text{Disc}(A)}(\text{ungel}(x. \text{gel}_x(\text{mod}(a), \text{mod}(a), \lambda^\mathbb{I}_{-}. \text{mod}(a)))) x \\ &= \text{loosen}_{\text{Disc}(A)}(\lambda^\mathbb{I}_{-}. \text{mod}(a)) x \\ &\rightsquigarrow (\lambda^\mathbb{I}_{-}. \text{mod}(a)) x \\ &= \text{mod}(a) \end{aligned}$$

For any $q: \text{Bridge}(\text{Bool}, d_0, d_1)$, the term $\lambda q. \lambda^\mathbb{I} y. \lambda^\mathbb{I} x. P_x(q x) y$ then has the following type.

$$\text{Path}(y. \text{Bridge}(\text{Bool}, P_0 d_0 y, P_1 d_1 y), \text{loosen}_{\text{Disc}(A)}(F q), q)$$

By the same argument used to prove Theorem 10.3.7, we can use singleton contractibility to replace $F$ by some $F' \in \text{Bridge}(\text{Disc}(A), d_0, d_1) \to \text{Path}(\text{Disc}(A), d_0, d_1)$ that satisfies the above with $P_0 d_0$ and $P_1 d_1$ replaced by reflexive paths, showing that the bridge type is a retract of the path type.

We therefore have, for example, that $((B : U) \to (\text{Disc}(A) \to B) \to B) \simeq \text{Disc}(A)$ as a consequence of Theorem 10.3.4. Polymorphic types like this one—where external point-wise types appear wrapped in Disc—are also amenable to the construction of “shadows”, as in the example below. (We leave the type-checking as an exercise to the reader.)

**Proposition 15.3.2.** For any $A : U$ and $c : \text{Glo}((B : U) \to (\text{Disc}(A) \to B) \to B)$, we have an induced function $\text{shadow}_A c \in (B : U) \to (A \to B) \to B$ @ pt defined as follows.

$$\text{shadow}_A c := \text{undisc}(\text{unmod}(c) (\text{Disc}(B)) (\text{map-disc} (\text{mod}(f))))$$

The codiscrete type satisfies a complementary property: it is *bridge-codiscrete*, in the sense that its bridge types are contractible. Here we see how the split operator allows us to construct bridges in the codiscrete type.

**Theorem 15.3.3.** For any type $(\text{glo} \mid A : U)$ and $c_0, c_1 : \text{Codisc}(A)$, the type of bridges $\text{Bridge}(\text{Codisc}(A), c_0, c_1)$ is contractible.