198

Programming with parametricity

Exploiting the isomorphism between bridges in path types and paths in bridge types (Lemma 9.2.3), this induces a family of dependent paths as follows.

$$(q : \text{Bridge}(\text{Bool}, b_0, b_1)) \to \text{Path}(y.\text{Bridge}(\text{Bool}, P_0 b_0 y, P_1 b_1 y), \lambda^1 x. L_x(F_x(q x)), q)$$

A quick calculation, reducing the extent term in $L_x$, reveals that $\lambda^1 x. L_x(F_x q x)$ is equal to $\text{loosen}_{\text{Bool}}(F q)$ in $\text{Path}(\text{Bool}, F_0 b_0, F_1 b_1)$.

We are almost at the end; we just have to deal with some endpoints. Abstracting slightly, we have shown that the following is inhabited for some pair of singletons $\langle b'_0, \eta_0 \rangle : (b'_0 : \text{Bool}) \times \text{Path}(\text{Bool}, b'_0, b_0)$ and $\langle b'_1, \eta_1 \rangle : (b'_1 : \text{Bool}) \times \text{Path}(\text{Bool}, b'_1, b_1)$.

$$(f : \text{Bridge}(\text{Bool}, b_0, b_1) \to \text{Path}(\text{Bool}, b'_0, b'_1)) \times$$

$$(q : \text{Bridge}(\text{Bool}, b_0, b_1)) \to \text{Path}(y.\text{Bridge}(\text{Bool}, \eta_0 y, \eta_1 y), \text{loosen}_{\text{Bool}}(f q), q)$$

Namely, we have a witness at $\eta_0 := P_0 b_0$ and $\eta_1 := P_1 b_1$. By singleton contractibility (Lemma 3.2.2), this choice of singletons is equal, up to a path, to the pair of reflexive singletons $\langle b_0, \lambda^1 \dots b_0 \rangle$ and $\langle b_1, \lambda^1 \dots b_1 \rangle$. By coercion, we thus obtain an element of the type above instantiated with that choice of singletons, which is exactly a right inverse for $\text{loosen}_{\text{Bool}}$. □

To give an idea of how this argument would proceed for inductive types more generally, we sketch the proof for Nat, showing how to define the map from bridges to paths.

Lemma 10.3.8. For any $n_0, n_1: \text{Nat}$, we have a map $\text{Bridge}(\text{Nat}, n_0, n_1) \to \text{Path}(\text{Nat}, n_0, n_1)$.

Proof. We begin again with Gel type for the path relation in Nat.

$$x : \text{I} \gg G_x := \text{Gel}_x(\text{Nat}, \text{Nat}, \text{Path}(\text{Nat}, -, -)) \text{ type}$$

We have canonical terms $z_x \in G_x$ and $s_x \in G_x \to G_x$ defined as follows.

$$z_x := \text{gel}_x(\text{zero}, \text{zero}, \lambda^1 \dots \text{zero})$$

$$s_x := \lambda g. \text{extent}_x(g; m_0.\text{suc}(m_0), m_1.\text{suc}(m_1), m_0.m_1.g'.y.S)$$

$$\text{where } S = \text{gel}_y(\text{suc}(m_0), \text{suc}(m_1), \lambda^1 z. \text{suc}(\text{ungel}(y.g'y)z))$$

The term $z_x$ carries the reflexive path zero $\rightsquigarrow$ zero, while $s_x$ takes a gel term containing a path $m_0 \rightsquigarrow m_1$ and returns a path $\text{suc}(m_0) \rightsquigarrow \text{suc}(m_1)$. Now we get a function from Nat to its path relation.

$$F_x := \lambda b. \text{elim}_{\text{Nat}}(\dots G_x; b; z_x, \dots g.s_x g) \in \text{Nat} \to G_x$$

Given a bridge $q : \text{Bridge}(\text{Nat}, n_0, n_1)$, we apply $F_x$ pointwise to get a path.

$$F := \text{ungel}(x.F_x(q x)) \in \text{Path}(\text{Nat}, F_0 n_0, F_1 n_1)$$

By inspection, we have $F_\varepsilon n = \text{elim}_{\text{Nat}}(\dots \text{Nat}; n; \text{zero}, \dots m.\text{suc}(m)) \in \text{Nat}$ for $\varepsilon \in \{0, 1\}$, and the latter is path-equal to $n$ by induction. □