Characterizing Church booleans 191

the left hand side is equal to $\text{elim}_{\text{Bool}}(\dots A; c \text{ Bool tt ff}; t, f)$. Our goal, then, is to relate the behavior of $c$ at Bool to its behavior at an arbitrary $A$.

To do so, we first single out a relation between Bool and $A$.

$$R := \lambda \langle b, a \rangle . \text{Path}(A, \text{elim}_{\text{Bool}}(\dots A; b; t, f), a) \in \text{Bool} \times A \rightarrow U$$

Notice that our goal is to show $R \langle c \text{ Bool tt ff}, c A t f \rangle$. To do so, we invoke parametricity: $c$ takes related arguments to related results. In parametric type theory, that slogan cashes out in our ability to form Gel types. In particular, given a fresh bridge interval variable $x$, we have the type $G_x := \text{Gel}_x(\text{Bool}, A, R)$ corresponding to $R$ with two canonical inhabitants.

$$\begin{aligned} t_x &:= \text{gel}_x(\text{tt}, t, \lambda^\mathbb{I} \dots t) \in G_x \\ f_x &:= \text{gel}_x(\text{ff}, f, \lambda^\mathbb{I} \dots f) \in G_x \end{aligned}$$

The first element expresses that $\text{tt}$ is related to $t$ in $R$, as witnessed by the term $\lambda^\mathbb{I} \dots t \in R \langle \text{tt}, t \rangle$; the second does the same for $\text{ff}$ and $f$.

By applying $c$ at this Gel type and its elements, we obtain a bridge relating $c \text{ Bool tt ff}$ and $c A t f$ over $x.G_x$; in effect, we have applied $c$ at the relation $R$.

$$\lambda^\mathbb{I} x . c G_x t_x f_x \in \text{Bridge}(x.G_x, c \text{ Bool tt ff}, c A t f)$$

Note the endpoints of this bridge: by definition, we have $G_0 = \text{Bool} \in U$, $t_0 = \text{tt} \in \text{Bool}$, and $f_0 = \text{ff} \in \text{Bool}$, likewise $G_1 = A \in U$, $t_1 = t \in A$, and $f_1 = f \in A$. At $0$, every relational term reduces to its $0$ endpoint; at $1$, to its $1$ endpoint. Finally, the ungel eliminator takes a bridge over a Gel type to a witness of the underlying relation.

$$\text{ungel}(x.c G_x t_x f_x) \in R \langle c \text{ Bool tt ff}, c A t f \rangle$$

This is exactly the type we needed to inhabit, and so we are satisfied.

It is perhaps instructive to consider how the inverse, constructed with parametricity primitives, evaluates when instantiated with a concrete $c : \mathbb{B}$. Say, for example, we take $\mathfrak{t}$. Then the term $\text{ungel}(x.\mathfrak{t} G_x t_x f_x)$ steps first to $\text{ungel}(x.t_x)$, then extracts the witness inside $t_x$ to produce the reflexive proof $\lambda^\mathbb{I} \dots t \in R \langle \mathfrak{t} \text{ Bool tt ff}, \mathfrak{t} A t f \rangle$. Likewise, instantiating $c$ with $\mathfrak{f}$ produces the reflexive path $\lambda^\mathbb{I} \dots f$ packaged in $f_x$. $\square$

Note that there are actually closed elements of $\mathbb{B}$ that are exactly equal neither to $\mathfrak{t}$ or to $\mathfrak{f}$. For example, we have the term $\lambda A . \lambda t . \lambda f . \text{coe}^{\frac{0}{\lambda} \cdot 1}(t) \in \mathbb{B}$; a coercion in a degenerate type line is only guaranteed to be equal to its input up to a path in general, not exactly, so this term is not exactly equal to $\mathfrak{t}$. Nevertheless, the result above shows it is equal to $\mathfrak{t}$ up to a path. Notice also that we obtain parametricity results despite the fact that