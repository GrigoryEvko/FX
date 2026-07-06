3.1. PRELIMINARIES

**Proposition 3.1.2.11.** *Any stratified Segal A-precategory is a homotopy colimit of objects of shape $[a, n]$ or $[e, 1]_t$.*

*Proof.* Let $C$ be a stratified Segal $A$-precategory. We have $C \cong \operatorname{colim}_{t\Delta[tB]/C} \_$. The result then follows from propositions 1.1.2.6, 2.1.2.3 and 3.1.1.4. $\square$

**3.1.2.12.** We now present the main way of constructing functors whose codomain is $\operatorname{tSeg}(A)$.

**Construction 3.1.2.13.** Suppose given a colimit preserving functor $G : A \times \Delta \to D$ in a complete category, an object $G(e, 1)'$ and a morphism $p : G(e, 1) \to G(e, 1)'$ such that for any object $d$ of $D$, $\operatorname{Hom}(p, d)$ is a monomorphism. We define the functor $\overline{G} : \operatorname{tSeg}(A) \to D$ as the unique colimit preserving functor such that $\overline{G}([e, 1]_t) := G(e, 1)'$ and for any $a, n$, $\overline{G}([a, n])$ fits in the following cocartesian square:

$$
\begin{array}{ccc}
\coprod_{i \in [n]} G(a, \{i\}) & \longrightarrow & G(a, [n]) \\
\downarrow & & \downarrow \\
\coprod_{i \in [n]} G(e, \{i\}) & \longrightarrow & \overline{G}([a, n])
\end{array}
$$

Remark that if the top horizontal morphism is a cofibration, the previous square is homotopy cocartesian.

**3.1.2.14.** In this model structure, the morphism $[e, 1]_t \to 1$ is a weak equivalence. For any $a \in A$ and $n \in \mathbb{N}$, we define $[e, 1]_t \vee [a, n]$ as the pushout:

$$
\begin{array}{ccc}
[e, 1] & \longrightarrow & [e, 1] \vee [a, n] \\
\downarrow & & \downarrow \\
[e, 1]_t & \longrightarrow & [e, 1]_t \vee [a, n]
\end{array}
$$

The canonical morphism $[e, 1]_t \cup [a, 1] \cup \ldots \cup [a, 1] \to [e, 1]_t \vee [a, n]$ is then a weak equivalence. By two out of three, and using the weak equivalence $[e, 1]_t \to 1$, this implies that $[e, 1]_t \vee [a, n] \to [a, n]$ is a weak equivalence.

We define similarly the object $[a, n] \vee [e, 1]_t$ that comes along with a weak equivalence $[a, n] \vee [e, 1]_t \to [a, n]$.

### 3.1.3 Gray module

**3.1.3.1.** Let $A$ be a category of stratified presheaves on an elegant Reedy category (as defined in paragraph 1.1.2.5 and section 2.1.2), endowed with a nice model structure

123